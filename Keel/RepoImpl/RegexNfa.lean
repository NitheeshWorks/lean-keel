import Keel.RepoImpl.Regex
import Std.Data.HashMap.Lemmas

/-!
# Regular expressions: the scan, compiled

`scan` rebuilds derivative terms at every character. `Nfa.build` does that
work once per pattern: it numbers the pattern and its partial derivatives
(`PD r`, at most one per character class), and for each term and context
slot stores its linear form (`lin`: each derivative with the class that
guards it) with the derivatives as numbers, and its nullability. A context
is what the assertions read of the characters on either side (`Side`); a
slot packs only the bits the pattern's assertions read, and a term's row is
computed only over the bits it reaches before its first character
(`reads`, `lin_agree`), then shared across the slots that agree on them. Matching
(`Nfa.run`) keeps a set of term numbers: per character, one class test per
live edge and an array of seen flags; no term is built, hashed or compared.
Within one call, the sets met are numbered and each step is cached
(`Nfa.crun`), so a text that revisits sets costs one lookup per character.

The tables carry their correctness as fields (`Nfa.hTrans`, `hNul`, `hFin`):
the numbering is checked when the pattern is compiled, and `build` gives
`none` (and the plain scan runs) if it is incomplete. `pd_eq_lin` shows the
linear form is `pd`; `Proofs/Regex.lean` proves `Nfa.accepts_eq`: the
compiled matcher is `accepts`. Everything here is total, with no fuel.
-/

namespace Keel

namespace Regex

/-- What the assertions read of the character on one side of a position:
whether there is none (an end of the text), whether it is a word character
(the dialect's, and ASCII's), and whether it is `\n` or `\r`. The same
record, read as a mask, says which of these bits a term reads. -/
structure Side where
  /-- There is no character: an end of the text. -/
  isEnd : Bool
  /-- A word character, as the dialect says (`CharClass.word`). -/
  word : Bool
  /-- An ASCII word character (`asciiWord`). -/
  asciiWord : Bool
  /-- `\n` -/
  lf : Bool
  /-- `\r` -/
  cr : Bool
  deriving DecidableEq, Repr, Inhabited

namespace Side

/-- No bit: the mask of a term that reads nothing. -/
def nothing : Side := ⟨false, false, false, false, false⟩

/-- The end of the text, as a side. -/
def atEnd : Side := ⟨true, false, false, false, false⟩

/-- The bits that both masks read. -/
def union (a b : Side) : Side :=
  ⟨a.isEnd || b.isEnd, a.word || b.word, a.asciiWord || b.asciiWord, a.lf || b.lf, a.cr || b.cr⟩

/-- Every bit `a` reads, `b` reads. -/
def le (a b : Side) : Bool :=
  (!a.isEnd || b.isEnd) && (!a.word || b.word) && (!a.asciiWord || b.asciiWord) &&
    (!a.lf || b.lf) && (!a.cr || b.cr)

/-- The bits of `s` that the mask `m` reads; the others cleared. -/
def proj (m s : Side) : Side :=
  ⟨m.isEnd && s.isEnd, m.word && s.word, m.asciiWord && s.asciiWord, m.lf && s.lf, m.cr && s.cr⟩

theorem proj_proj (m s : Side) : m.proj (m.proj s) = m.proj s := by
  simp only [proj, ← Bool.and_assoc, Bool.and_self]

end Side

/-- What an assertion reads of the character on one side of a position. -/
@[inline] def ctx (κ : Type) [CharClass κ] (p : Option Char) : Side :=
  ⟨p.isNone, wordAt (CharClass.word κ) p, wordAt asciiWord p, p == some '\n', p == some '\r'⟩

theorem ctx_none (κ : Type) [CharClass κ] : ctx κ none = Side.atEnd := rfl

theorem ctx_some_isEnd (κ : Type) [CharClass κ] (c : Char) : (ctx κ (some c)).isEnd = false := rfl

/-- `Assertion.holds`, on the two sides' bits. -/
def Assertion.holdsB : Assertion → Side → Side → Bool
  | .start, p, _ => p.isEnd
  | .finish, _, n => n.isEnd
  | .wordBoundary, p, n => p.word != n.word
  | .notWordBoundary, p, n => p.word == n.word
  | .wordStart, p, n => !p.word && n.word
  | .wordEnd, p, n => p.word && !n.word
  | .lineStart, p, _ => p.isEnd || p.lf
  | .lineEnd, _, n => n.isEnd || n.lf
  | .lineStartCRLF, p, n => p.isEnd || p.lf || (p.cr && !n.lf)
  | .lineEndCRLF, p, n => n.isEnd || n.cr || (n.lf && !p.cr)
  | .wordBoundaryAscii, p, n => p.asciiWord != n.asciiWord
  | .notWordBoundaryAscii, p, n => p.asciiWord == n.asciiWord
  | .wordStartAscii, p, n => !p.asciiWord && n.asciiWord
  | .wordEndAscii, p, n => p.asciiWord && !n.asciiWord
  | .wordStartHalf, p, _ => !p.word
  | .wordEndHalf, _, n => !n.word
  | .wordStartHalfAscii, p, _ => !p.asciiWord
  | .wordEndHalfAscii, _, n => !n.asciiWord

theorem Assertion.holds_eq (κ : Type) [CharClass κ] (a : Assertion) (p n : Option Char) :
    a.holds (CharClass.word κ) p n = a.holdsB (ctx κ p) (ctx κ n) := by
  cases a <;> rfl

/-- The bits an assertion reads of the character before and of the one
after; whether the one after exists is left out, as the tables always know
it (a character is read, or the text has ended). -/
def Assertion.reads : Assertion → Side × Side
  | .start => (⟨true, false, false, false, false⟩, .nothing)
  | .finish => (.nothing, .nothing)
  | .wordBoundary | .notWordBoundary | .wordStart | .wordEnd =>
    (⟨false, true, false, false, false⟩, ⟨false, true, false, false, false⟩)
  | .lineStart => (⟨true, false, false, true, false⟩, .nothing)
  | .lineEnd => (.nothing, ⟨false, false, false, true, false⟩)
  | .lineStartCRLF => (⟨true, false, false, true, true⟩, ⟨false, false, false, true, false⟩)
  | .lineEndCRLF => (⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩)
  | .wordBoundaryAscii | .notWordBoundaryAscii | .wordStartAscii | .wordEndAscii =>
    (⟨false, false, true, false, false⟩, ⟨false, false, true, false, false⟩)
  | .wordStartHalf => (⟨false, true, false, false, false⟩, .nothing)
  | .wordEndHalf => (.nothing, ⟨false, true, false, false, false⟩)
  | .wordStartHalfAscii => (⟨false, false, true, false, false⟩, .nothing)
  | .wordEndHalfAscii => (.nothing, ⟨false, false, true, false, false⟩)

/-- **An assertion reads only its bits**: two contexts that agree on them
(and on whether the text has ended after) give the same answer. -/
theorem Assertion.holdsB_agree (a : Assertion) {mp mn pc pc' nc nc' : Side}
    (h : (a.reads.1.le mp && a.reads.2.le mn) = true)
    (hp : mp.proj pc = mp.proj pc') (hn : mn.proj nc = mn.proj nc') (he : nc.isEnd = nc'.isEnd) :
    a.holdsB pc nc = a.holdsB pc' nc' := by
  obtain ⟨_, _, _, _, _⟩ := mp; obtain ⟨_, _, _, _, _⟩ := mn
  simp only [Side.proj, Side.mk.injEq] at hp hn
  cases a <;> simp_all [reads, Side.le, Side.nothing, holdsB]

variable {κ : Type} [CharClass κ] [DecidableEq κ]


/-- `nullable`, on the two sides' bits. -/
@[specialize]
def nullB (pc nc : Side) : Regex κ → Bool
  | empty => false
  | eps => true
  | cls _ => false
  | assert a => a.holdsB pc nc
  | alt r s => nullB pc nc r || nullB pc nc s
  | cat r s => nullB pc nc r && nullB pc nc s
  | star _ => true

omit [DecidableEq κ] in
theorem nullable_eq (p n : Option Char) : ∀ r : Regex κ, nullable p n r = nullB (ctx κ p) (ctx κ n) r
  | empty | eps | cls _ | star _ => rfl
  | assert a => Assertion.holds_eq κ a p n
  | alt r s | cat r s => by simp only [nullable, nullB, nullable_eq p n r, nullable_eq p n s]

/-- Whether `r` can match the empty string in some context (assertions
taken as holding): when not, `nullB` is false in every context. -/
def canNull : Regex κ → Bool
  | empty | cls _ => false
  | eps | assert _ | star _ => true
  | alt r s => canNull r || canNull s
  | cat r s => canNull r && canNull s

omit [CharClass κ] [DecidableEq κ] in
theorem canNull_of_nullB {pc nc : Side} : ∀ {r : Regex κ}, nullB pc nc r = true → canNull r = true
  | empty, h | cls _, h => by simp [nullB] at h
  | eps, _ | assert _, _ | star _, _ => rfl
  | alt r s, h => by
    simp only [nullB, Bool.or_eq_true] at h
    simp only [canNull, Bool.or_eq_true]
    exact h.imp canNull_of_nullB canNull_of_nullB
  | cat r s, h => by
    simp only [nullB, Bool.and_eq_true] at h
    simp only [canNull, Bool.and_eq_true]
    exact ⟨canNull_of_nullB h.1, canNull_of_nullB h.2⟩

omit [CharClass κ] [DecidableEq κ] in
theorem nullB_of_canNull {pc nc : Side} {r : Regex κ} (h : canNull r = false) : nullB pc nc r = false := by
  cases hn : nullB pc nc r
  · rfl
  · rw [canNull_of_nullB hn] at h; cases h

/-- The assertions of `r` that can be read before its first character (the
ones `nullB` and `lin` look at) read only the bits in `mp` (of the character
before) and `mn` (of the character after). -/
def within (mp mn : Side) : Regex κ → Bool
  | assert a => a.reads.1.le mp && a.reads.2.le mn
  | alt r s => within mp mn r && within mp mn s
  | cat r s => within mp mn r && (!canNull r || within mp mn s)
  | star r => within mp mn r
  | _ => true

/-- The bits that the assertions of `r` read before its first character: a
term's own masks. -/
def reads : Regex κ → Side × Side
  | assert a => a.reads
  | alt r s => ((reads r).1.union (reads s).1, (reads r).2.union (reads s).2)
  | cat r s => if canNull r then ((reads r).1.union (reads s).1, (reads r).2.union (reads s).2) else reads r
  | star r => reads r
  | _ => (.nothing, .nothing)

omit [CharClass κ] [DecidableEq κ] in
/-- `nullB` reads only the bits that the assertions it reaches read. -/
theorem nullB_agree {mp mn pc pc' nc nc' : Side} (hp : mp.proj pc = mp.proj pc')
    (hn : mn.proj nc = mn.proj nc') (he : nc.isEnd = nc'.isEnd) :
    ∀ r : Regex κ, within mp mn r = true → nullB pc nc r = nullB pc' nc' r
  | empty, _ | eps, _ | cls _, _ | star _, _ => rfl
  | assert a, h => a.holdsB_agree h hp hn he
  | alt r s, h => by
    simp only [within, Bool.and_eq_true] at h
    simp only [nullB, nullB_agree hp hn he r h.1, nullB_agree hp hn he s h.2]
  | cat r s, h => by
    simp only [within, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hr, hs⟩ := h
    rcases hs with hc | hs
    · simp only [nullB, nullB_of_canNull hc, Bool.false_and]
    · simp only [nullB, nullB_agree hp hn he r hr, nullB_agree hp hn he s hs]

/-- Antimirov's linear form, in context: the derivatives of `r` by a
character with their guarding class, when the character before has bits
`pc` and the character read has bits `nc`. -/
@[specialize]
def lin (pc nc : Side) : Regex κ → List (κ × Regex κ)
  | empty => []
  | eps => []
  | cls k => [(k, eps)]
  | assert _ => []
  | alt r s => lin pc nc r ++ lin pc nc s
  | cat r s =>
    (lin pc nc r).map (fun kq => (kq.1, seq kq.2 s)) ++ (if nullB pc nc r then lin pc nc s else [])
  | star r => (lin pc nc r).map (fun kq => (kq.1, seq kq.2 (star r)))

omit [CharClass κ] in
/-- `lin` reads only the bits that the assertions it reaches read. -/
theorem lin_agree {mp mn pc pc' nc nc' : Side} (hp : mp.proj pc = mp.proj pc')
    (hn : mn.proj nc = mn.proj nc') (he : nc.isEnd = nc'.isEnd) :
    ∀ r : Regex κ, within mp mn r = true → lin pc nc r = lin pc' nc' r
  | empty, _ | eps, _ | cls _, _ | assert _, _ => rfl
  | alt r s, h => by
    simp only [within, Bool.and_eq_true] at h
    simp only [lin, lin_agree hp hn he r h.1, lin_agree hp hn he s h.2]
  | cat r s, h => by
    simp only [within, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hr, hs⟩ := h
    rcases hs with hc | hs
    · simp only [lin, lin_agree hp hn he r hr, nullB_of_canNull hc, Bool.false_eq_true, ↓reduceIte]
    · simp only [lin, lin_agree hp hn he r hr, lin_agree hp hn he s hs, nullB_agree hp hn he r hr]
  | star r, h => by
    simp only [within] at h
    simp only [lin, lin_agree hp hn he r h]

/-- The derivatives by `c` that the linear form's classes let through. -/
def pick (c : Char) (l : List (κ × Regex κ)) : List (Regex κ) :=
  l.filterMap fun kq => if CharClass.test kq.1 c then some kq.2 else none

/-- **The partial derivatives are the linear form, filtered by `c`.** -/
theorem pd_eq_lin (p : Option Char) (c : Char) : ∀ r : Regex κ, pd p c r = pick c (lin (ctx κ p) (ctx κ (some c)) r)
  | empty | eps | assert _ => rfl
  | cls k => by simp only [pd, lin, pick, List.filterMap_cons, List.filterMap_nil]; split <;> rfl
  | alt r s => by simp only [pd, lin, pick, List.filterMap_append, pd_eq_lin p c r, pd_eq_lin p c s]
  | cat r s => by
    have hn : nullable p (some c) r = nullB (ctx κ p) (ctx κ (some c)) r := nullable_eq p (some c) r
    simp only [pd, lin, pick, List.filterMap_append, pd_eq_lin p c r, pd_eq_lin p c s, hn]
    congr 1
    · simp only [List.filterMap_map, List.map_filterMap]
      congr 1; funext kq; simp only [Function.comp]; split <;> simp_all
    · split <;> rfl
  | star r => by
    simp only [pd, lin, pick, pd_eq_lin p c r, List.filterMap_map, List.map_filterMap]
    congr 1; funext kq; simp only [Function.comp]; split <;> simp_all


/-! ## Sets of term numbers -/

/-- `l` without repeats (numbers below `n`; any others are kept as they are). -/
def dedupIds (n : Nat) (l : List Nat) : List Nat := go (Array.replicate n false) [] l
where
  go (seen : Array Bool) (acc : List Nat) : List Nat → List Nat
    | [] => acc
    | j :: l => if seen[j]?.getD false then go seen acc l else go (seen.set! j true) (j :: acc) l

theorem dedupIds_go_mem : ∀ (l : List Nat) (seen : Array Bool) (acc : List Nat),
    (∀ x, seen[x]?.getD false = true → x ∈ acc) → ∀ x, x ∈ dedupIds.go seen acc l ↔ x ∈ acc ∨ x ∈ l
  | [], _, _, _, x => by simp [dedupIds.go]
  | j :: l, seen, acc, h, x => by
    simp only [dedupIds.go]
    split
    · rename_i hj
      rw [dedupIds_go_mem l seen acc h x]
      have := h j hj
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl this
        · exact .inr h
    · rw [dedupIds_go_mem l _ (j :: acc) ?_ x]
      · simp only [List.mem_cons]
        constructor
        · rintro ((rfl | h) | h)
          · exact .inr (.inl rfl)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | rfl | h)
          · exact .inl (.inr h)
          · exact .inl (.inl rfl)
          · exact .inr h
      · intro y hy
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hy
        split at hy
        · subst_vars; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h y hy)

theorem mem_dedupIds (n : Nat) (l : List Nat) (x : Nat) : x ∈ dedupIds n l ↔ x ∈ l := by
  unfold dedupIds
  rw [dedupIds_go_mem l _ [] (fun y hy => by simp [Array.getElem?_replicate] at hy; split at hy <;> simp at hy) x]
  simp


/-! ## The compiled matcher

The tables of a pattern have a row per context its terms can tell apart: the
masks `mp` and `mn` (`reads`) say which bits of the character before and of
the one after any assertion of the pattern reads, and a context's slot packs
just those bits (`code`). A pattern with `^` alone has two slots, one with
word boundaries eight, one with no assertion but `$` one. -/

/-- Append a bit to a code, if the mask reads it. -/
@[inline] def pushBit (sel v : Bool) (acc : Nat) : Nat := if sel then 2 * acc + v.toNat else acc

/-- Take the last bit off a code, if the mask read it. -/
@[inline] def popBit (sel : Bool) (k : Nat) : Bool × Nat := if sel then (k % 2 == 1, k / 2) else (false, k)

theorem popBit_pushBit (sel v : Bool) (acc : Nat) : popBit sel (pushBit sel v acc) = (sel && v, acc) := by
  cases sel <;> cases v <;> simp [popBit, pushBit] <;> omega

/-- The number of codes, for each bit the mask reads a doubling. -/
@[inline] def widen (sel : Bool) (b : Nat) : Nat := if sel then 2 * b else b

theorem pushBit_lt {sel v : Bool} {acc b : Nat} (h : acc < b) : pushBit sel v acc < widen sel b := by
  cases sel <;> cases v <;> simp [pushBit, widen] <;> omega

/-- A side's slot: the bits of `s` that the mask `m` reads. -/
@[inline] def code (m s : Side) : Nat :=
  pushBit m.cr s.cr (pushBit m.lf s.lf (pushBit m.asciiWord s.asciiWord (pushBit m.word s.word
    (pushBit m.isEnd s.isEnd 0))))

/-- The slot's side, with the bits the mask does not read cleared. -/
def decode (m : Side) (k : Nat) : Side :=
  let cr := popBit m.cr k
  let lf := popBit m.lf cr.2
  let aw := popBit m.asciiWord lf.2
  let w := popBit m.word aw.2
  ⟨(popBit m.isEnd w.2).1, w.1, aw.1, lf.1, cr.1⟩

theorem decode_code (m s : Side) : decode m (code m s) = m.proj s := by
  simp only [decode, code, popBit_pushBit, Side.proj]

/-- The number of slots of a mask. -/
@[inline] def Side.size (m : Side) : Nat := widen m.cr (widen m.lf (widen m.asciiWord (widen m.word (widen m.isEnd 1))))

theorem code_lt (m s : Side) : code m s < m.size :=
  pushBit_lt (pushBit_lt (pushBit_lt (pushBit_lt (pushBit_lt Nat.zero_lt_one))))

theorem Side.size_pos (m : Side) : 0 < m.size := Nat.lt_of_le_of_lt (Nat.zero_le _) (code_lt m m)

/-- The slot of a context, before (`mp`) and after (`mn`) a position. -/
@[inline] def slot (mp mn pc nc : Side) : Nat := code mp pc + mp.size * code mn nc

/-- The slot's context. -/
def unslot (mp mn : Side) (k : Nat) : Side × Side := (decode mp (k % mp.size), decode mn (k / mp.size))

theorem unslot_slot (mp mn pc nc : Side) : unslot mp mn (slot mp mn pc nc) = (mp.proj pc, mn.proj nc) := by
  have h := code_lt mp pc
  have hs := Side.size_pos mp
  simp only [unslot, slot, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h, Nat.add_mul_div_left _ _ hs,
    Nat.div_eq_of_lt h, Nat.zero_add, decode_code]

theorem slot_lt (mp mn pc nc : Side) : slot mp mn pc nc < mp.size * mn.size := by
  have h₁ := code_lt mp pc
  have h₂ := code_lt mn nc
  unfold slot
  calc code mp pc + mp.size * code mn nc < mp.size + mp.size * code mn nc := by omega
    _ = mp.size * (code mn nc + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ ≤ mp.size * mn.size := Nat.mul_le_mul_left _ h₂

omit [CharClass κ] in
/-- A projected context reads as the context itself, for a term within the
masks, when a character is read. -/
theorem lin_unslot {mp mn pc nc : Side} (hn : nc.isEnd = false) {t : Regex κ} (h : within mp mn t = true) :
    lin (unslot mp mn (slot mp mn pc nc)).1 (unslot mp mn (slot mp mn pc nc)).2 t = lin pc nc t := by
  rw [unslot_slot]
  obtain ⟨_, _, _, _, _⟩ := mn
  exact lin_agree (Side.proj_proj _ _) (Side.proj_proj _ _) (by simp [Side.proj, hn]) t h

omit [CharClass κ] [DecidableEq κ] in
theorem nullB_unslot {mp mn pc nc : Side} (hn : nc.isEnd = false) {t : Regex κ} (h : within mp mn t = true) :
    nullB (unslot mp mn (slot mp mn pc nc)).1 (unslot mp mn (slot mp mn pc nc)).2 t = nullB pc nc t := by
  rw [unslot_slot]
  obtain ⟨_, _, _, _, _⟩ := mn
  exact nullB_agree (Side.proj_proj _ _) (Side.proj_proj _ _) (by simp [Side.proj, hn]) t h

theorem Side.proj_proj_of_le {a m : Side} (h : a.le m = true) (s : Side) : a.proj (m.proj s) = a.proj s := by
  obtain ⟨_, _, _, _, _⟩ := a; obtain ⟨_, _, _, _, _⟩ := m
  simp only [Side.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  simp only [Side.proj, Side.mk.injEq]
  rcases h with ⟨⟨⟨⟨h1 | h1, h2 | h2⟩, h3 | h3⟩, h4 | h4⟩, h5 | h5⟩ <;> simp [*]

omit [CharClass κ] in
/-- A term reads the same in a context and in its projection on masks that
cover the term's own. -/
theorem lin_proj {tp tn mp mn : Side} {t : Regex κ} (hw : within tp tn t = true) (hp : tp.le mp = true)
    (hn : tn.le mn = true) (pc nc : Side) (he : nc.isEnd = false) :
    lin (mp.proj pc) (mn.proj nc) t = lin pc nc t :=
  lin_agree (Side.proj_proj_of_le hp pc) (Side.proj_proj_of_le hn nc) (by simp [Side.proj, he]) t hw

omit [CharClass κ] [DecidableEq κ] in
theorem nullB_proj {tp tn mp mn : Side} {t : Regex κ} (hw : within tp tn t = true) (hp : tp.le mp = true)
    (hn : tn.le mn = true) (pc nc : Side) (he : nc.isEnd = false) :
    nullB (mp.proj pc) (mn.proj nc) t = nullB pc nc t :=
  nullB_agree (Side.proj_proj_of_le hp pc) (Side.proj_proj_of_le hn nc) (by simp [Side.proj, he]) t hw

/-- The pattern compiled once: its derivative terms numbered (`terms[0]` is
the pattern), the masks of the bits its assertions read, and for each term
and context slot, its linear form with the derivatives as numbers, and
whether it is nullable before a character and at the end. The fields after
the tables say they are right. -/
structure Nfa (r : Regex κ) where
  terms : Array (Regex κ)
  /-- The bits of the character before that the terms read. -/
  mp : Side
  /-- The bits of the character after that the terms read. -/
  mn : Side
  trans : Array (Array (Array (κ × Nat)))
  nul : Array (Array Bool)
  fin : Array (Array Bool)
  start : terms[0]? = some r
  hTrans : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → ∀ (pc nc : Side), nc.isEnd = false →
    ((trans[j]?.bind (·[slot mp mn pc nc]?)).getD #[]).toList.map (fun e => (e.1, terms[e.2]?)) =
      (lin pc nc t).map (fun kq => (kq.1, some kq.2))
  hNul : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → ∀ (pc nc : Side), nc.isEnd = false →
    (nul[j]?.bind (·[slot mp mn pc nc]?)).getD false = nullB pc nc t
  hFin : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → ∀ (pc : Side),
    (fin[j]?.bind (·[code mp pc]?)).getD false = nullB pc .atEnd t
  /-- The slot part of each ASCII character as the character before. -/
  pcodes : Array Nat
  /-- The slot part of each ASCII character as the character read. -/
  ncodes : Array Nat
  hP : ∀ (k v : Nat), pcodes[k]? = some v → v = code mp (ctx κ (some (Char.ofNat k)))
  hN : ∀ (k v : Nat), ncodes[k]? = some v → v = mp.size * code mn (ctx κ (some (Char.ofNat k)))

namespace Nfa

variable {r : Regex κ} (N : Nfa r) (m : Mode)

/-- The term numbers a step adds for a match starting after the character
read: the pattern's, unless the start is anchored. -/
def restart : List Nat := if m.anchorStart then [] else [0]

/-- The slot part of the character before: from the table for an ASCII
character. -/
@[inline] def pcode (p : Option Char) : Nat :=
  match p with
  | some c =>
    match N.pcodes[c.toNat]? with
    | some v => v
    | none => code N.mp (ctx κ (some c))
  | none => code N.mp (ctx κ none)

/-- The slot part of the character read: from the table for an ASCII
character. -/
@[inline] def ncode (c : Char) : Nat :=
  match N.ncodes[c.toNat]? with
  | some v => v
  | none => N.mp.size * code N.mn (ctx κ (some c))

theorem pcode_eq (p : Option Char) : N.pcode p = code N.mp (ctx κ p) := by
  unfold pcode
  split
  · rename_i c
    split
    · rename_i v h; rw [N.hP _ _ h, Char.ofNat_toNat]
    · rfl
  · rfl

theorem ncode_eq (c : Char) : N.ncode c = N.mp.size * code N.mn (ctx κ (some c)) := by
  unfold ncode
  split
  · rename_i v h; rw [N.hN _ _ h, Char.ofNat_toNat]
  · rfl

theorem slot_eq (p : Option Char) (c : Char) : N.pcode p + N.ncode c = slot N.mp N.mn (ctx κ p) (ctx κ (some c)) := by
  rw [pcode_eq, ncode_eq]; rfl

/-- The numbered derivatives of term `j`, with their classes, in slot `k`. -/
@[inline] def edges (j k : Nat) : Array (κ × Nat) :=
  (N.trans.getD j #[]).getD k #[]

/-- Whether term `j` is nullable before a character, in slot `k`. -/
@[inline] def nulAt (k j : Nat) : Bool :=
  if j < N.terms.size then (N.nul.getD j #[]).getD k false else false

/-- Whether term `j` is nullable at the end, after a character with code `pk`. -/
@[inline] def finAt (pk j : Nat) : Bool :=
  if j < N.terms.size then (N.fin.getD j #[]).getD pk false else false

theorem getD2 {β : Type} (a : Array (Array β)) (j k : Nat) (d : β) :
    (a.getD j #[]).getD k d = (a[j]?.bind (·[k]?)).getD d := by
  simp only [Array.getD_eq_getD_getElem?]
  cases a[j]? <;> simp

theorem edges_eq (j k : Nat) :
    N.edges j k = (N.trans[j]?.bind (·[k]?)).getD #[] := getD2 _ _ _ _

/-- The derivatives of the set by `c` in slot `k`, as numbers, and `restart`. -/
def next (k : Nat) (c : Char) (S : List Nat) : List Nat :=
  dedupIds N.terms.size (restart m ++ S.flatMap fun j =>
    if j < N.terms.size then
      (N.edges j k).toList.filterMap fun e => if CharClass.test e.1 c then some e.2 else none
    else [])

/-- Add an edge's target if its class takes `c` and it is not in yet. -/
@[inline] def addEdge (c : Char) (sa : Array Bool × List Nat) (e : κ × Nat) : Array Bool × List Nat :=
  if CharClass.test e.1 c then
    if sa.1[e.2]?.getD false then sa else (sa.1.set! e.2 true, e.2 :: sa.2)
  else sa

/-- `addEdge` over the edges from `i` on, with the flags and the set as
separate arguments so the flag array is updated in place. -/
@[specialize]
def edgeLoop (es : Array (κ × Nat)) (c : Char) (i : Nat) (seen : Array Bool) (acc : List Nat) :
    Array Bool × List Nat :=
  if h : i < es.size then
    let e := es[i]
    if CharClass.test e.1 c then
      if seen[e.2]?.getD false then edgeLoop es c (i + 1) seen acc
      else edgeLoop es c (i + 1) (seen.set! e.2 true) (e.2 :: acc)
    else edgeLoop es c (i + 1) seen acc
  else (seen, acc)
termination_by es.size - i

omit [DecidableEq κ] in
theorem edgeLoop_eq (es : Array (κ × Nat)) (c : Char) (i : Nat) (seen : Array Bool) (acc : List Nat) :
    edgeLoop es c i seen acc = (es.toList.drop i).foldl (addEdge c) (seen, acc) := by
  unfold edgeLoop
  split
  · rename_i h
    rw [List.drop_eq_getElem_cons (by simpa using h)]
    simp only [List.foldl_cons, addEdge, Array.getElem_toList]
    split
    · split
      · exact edgeLoop_eq es c (i + 1) seen acc
      · exact edgeLoop_eq es c (i + 1) _ _
    · exact edgeLoop_eq es c (i + 1) seen acc
  · rename_i h
    rw [List.drop_of_length_le (by simp; omega)]
    rfl
termination_by es.size - i

/-- `next`'s work in one pass: every live term's edges, into a seen-flag
array and the new set. -/
@[specialize]
def stepGo (k : Nat) (c : Char) : List Nat → Array Bool × List Nat → Array Bool × List Nat
  | [], sa => sa
  | j :: S, (seen, acc) =>
    stepGo k c S (if j < N.terms.size then edgeLoop (N.edges j k) c 0 seen acc else (seen, acc))

/-- `next`, with no intermediate lists (`nextFast_mem`). -/
@[specialize]
def nextFast (k : Nat) (c : Char) (S : List Nat) : List Nat :=
  (N.stepGo k c S
    (if m.anchorStart then (Array.replicate N.terms.size false, [])
     else ((Array.replicate N.terms.size false).set! 0 true, [0]))).2

/-- What the seen flags promise: a flagged number is in the set. -/
def SeenOk (sa : Array Bool × List Nat) : Prop := ∀ x, sa.1[x]?.getD false = true → x ∈ sa.2

omit [DecidableEq κ] in
theorem addEdge_spec (c : Char) (sa : Array Bool × List Nat) (e : κ × Nat) (h : SeenOk sa) :
    SeenOk (addEdge c sa e) ∧ ∀ x, x ∈ (addEdge c sa e).2 ↔ x ∈ sa.2 ∨ (CharClass.test e.1 c = true ∧ e.2 = x) := by
  unfold addEdge
  split
  · rename_i ht
    split
    · rename_i hs
      refine ⟨h, fun x => ⟨.inl, ?_⟩⟩
      rintro (hx | ⟨-, rfl⟩)
      · exact hx
      · exact h _ hs
    · refine ⟨?_, fun x => ?_⟩
      · intro y hy
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hy
        split at hy
        · subst_vars; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h y hy)
      · simp only [List.mem_cons, ht, true_and]
        constructor
        · rintro (rfl | hx)
          · exact .inr rfl
          · exact .inl hx
        · rintro (hx | rfl)
          · exact .inr hx
          · exact .inl rfl
  · rename_i ht
    refine ⟨h, fun x => ⟨.inl, ?_⟩⟩
    rintro (hx | ⟨hc, -⟩)
    · exact hx
    · exact absurd hc ht

omit [DecidableEq κ] in
theorem foldl_addEdge (c : Char) : ∀ (es : List (κ × Nat)) (sa : Array Bool × List Nat), SeenOk sa →
    SeenOk (es.foldl (addEdge c) sa) ∧
      ∀ x, x ∈ (es.foldl (addEdge c) sa).2 ↔ x ∈ sa.2 ∨ ∃ e ∈ es, CharClass.test e.1 c = true ∧ e.2 = x
  | [], sa, h => ⟨h, fun x => by simp⟩
  | e :: es, sa, h => by
    obtain ⟨h1, h2⟩ := addEdge_spec c sa e h
    obtain ⟨h3, h4⟩ := foldl_addEdge c es _ h1
    refine ⟨h3, fun x => ?_⟩
    simp only [List.foldl_cons, h4, h2, List.mem_cons]
    constructor
    · rintro ((hx | hx) | ⟨e', he', hx⟩)
      · exact .inl hx
      · exact .inr ⟨e, .inl rfl, hx⟩
      · exact .inr ⟨e', .inr he', hx⟩
    · rintro (hx | ⟨e', (rfl | he'), hx⟩)
      · exact .inl (.inl hx)
      · exact .inl (.inr hx)
      · exact .inr ⟨e', he', hx⟩

theorem stepGo_spec (k : Nat) (c : Char) : ∀ (S : List Nat) (sa : Array Bool × List Nat),
    SeenOk sa → ∀ x, x ∈ (N.stepGo k c S sa).2 ↔
      x ∈ sa.2 ∨ ∃ j ∈ S, j < N.terms.size ∧ ∃ e ∈ (N.edges j k).toList, CharClass.test e.1 c = true ∧ e.2 = x
  | [], sa, _, x => by simp [stepGo]
  | j :: S, sa, h, x => by
    simp only [stepGo]
    split
    · rename_i hj
      rw [edgeLoop_eq, List.drop_zero]
      obtain ⟨h1, h2⟩ := foldl_addEdge c (N.edges j k).toList sa h
      rw [stepGo_spec k c S _ h1 x, h2]
      simp only [List.mem_cons]
      constructor
      · rintro ((hx | hx) | ⟨j', hj', hx⟩)
        · exact .inl hx
        · exact .inr ⟨j, .inl rfl, hj, hx⟩
        · exact .inr ⟨j', .inr hj', hx⟩
      · rintro (hx | ⟨j', (rfl | hj'), hl, hx⟩)
        · exact .inl (.inl hx)
        · exact .inl (.inr hx)
        · exact .inr ⟨j', hj', hl, hx⟩
    · rename_i hj
      rw [stepGo_spec k c S _ h x]
      simp only [List.mem_cons]
      constructor
      · rintro (hx | ⟨j', hj', hx⟩)
        · exact .inl hx
        · exact .inr ⟨j', .inr hj', hx⟩
      · rintro (hx | ⟨j', (rfl | hj'), hl, hx⟩)
        · exact .inl hx
        · exact absurd hl hj
        · exact .inr ⟨j', hj', hl, hx⟩

theorem nextFast_mem (k : Nat) (c : Char) (S : List Nat) (x : Nat) :
    x ∈ N.nextFast m k c S ↔ x ∈ N.next m k c S := by
  unfold nextFast next
  rw [N.stepGo_spec k c S _ ?_ x, mem_dedupIds]
  · have hr : x ∈ (if m.anchorStart then ((Array.replicate N.terms.size false, []) : Array Bool × List Nat)
        else ((Array.replicate N.terms.size false).set! 0 true, [0])).2 ↔ x ∈ restart m := by
      unfold restart; split <;> rfl
    rw [hr]
    simp only [List.mem_append, List.mem_flatMap]
    constructor
    · rintro (hx | ⟨j, hj, hl, e, he, hc, rfl⟩)
      · exact .inl hx
      · refine .inr ⟨j, hj, ?_⟩
        simp only [hl, ↓reduceIte]; rw [List.mem_filterMap]
        exact ⟨e, he, by simp [hc]⟩
    · rintro (hx | ⟨j, hj, hx⟩)
      · exact .inl hx
      · split at hx
        · rename_i hl
          rw [List.mem_filterMap] at hx
          obtain ⟨e, he, hex⟩ := hx
          split at hex
          · rename_i hc; simp only [Option.some.injEq] at hex
            exact .inr ⟨j, hj, hl, e, he, hc, hex⟩
          · cases hex
        · cases hx
  · intro y hy
    by_cases ha : m.anchorStart = true
    · simp only [ha, ite_true, Array.getElem?_replicate] at hy; split at hy <;> simp at hy
    · simp only [ha, Bool.false_eq_true, ite_false, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds, Array.getElem?_replicate] at hy ⊢
      split at hy
      · subst_vars; exact List.mem_singleton_self _
      · split at hy <;> simp at hy

/-- The scan over term numbers. -/
@[specialize]
def run : Option Char → List Char → List Nat → Bool
  | p, [], S => S.any (N.finAt (N.pcode p))
  | p, c :: cs, S =>
    let k := N.pcode p + N.ncode c
    if !m.anchorEnd && S.any (N.nulAt k) then true
    else run (some c) cs (N.nextFast m k c S)

/-! ### Caching the steps of one call

Within a call the term sets met repeat (for `^(a{1,50})+$` on a run of
`a`, after the first fifty characters every set has been seen), so the
sets are numbered as they appear and each step is cached by (set number,
the slot code of the character before, the character). A cached step is one
hash lookup. Past `maxStates` sets nothing more is cached and the rest of
the text runs `run` directly, so a pattern whose sets never repeat costs one
plain step per character. `Cache.good` says every cached step is `run`'s. -/

/-- The cache key: a set's number, the slot code of the character before
(`pcode`), the character. -/
abbrev Key := Nat × Nat × Char

/-- The sets met so far, an index from a set to its number, and the cached
steps. -/
structure Cache where
  states : Array (List Nat)
  index : Std.HashMap (List Nat) Nat
  trans : Std.HashMap Key (Bool × Nat)
  indexed : ∀ (S : List Nat) (j : Nat), index[S]? = some j → states[j]? = some S
  good : ∀ (i pk : Nat) (c : Char) (acc : Bool) (j : Nat), trans[(i, pk, c)]? = some (acc, j) →
    ∃ S, states[i]? = some S ∧ acc = S.any (N.nulAt (pk + N.ncode c)) ∧
      states[j]? = some (N.nextFast m (pk + N.ncode c) c S)

/-- More sets than this in one call and nothing more is cached. -/
def maxStates : Nat := 1024

namespace Cache

variable {N} {m}

/-- One set and no steps. -/
def start (S : List Nat) : Cache N m where
  states := #[S]
  index := (∅ : Std.HashMap (List Nat) Nat).insert S 0
  trans := ∅
  indexed := by
    intro S' j h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk; simp only [beq_iff_eq] at hk; subst hk
      simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  good := by intro i pk c acc j h; simp at h

/-- Add a set at the end. -/
def push (d : Cache N m) (S : List Nat) : Cache N m where
  states := d.states.push S
  index := d.index.insert S d.states.size
  trans := d.trans
  indexed := by
    intro S' j h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk; simp only [beq_iff_eq] at hk; subst hk
      simp only [Option.some.injEq] at h; subst h; simp
    · have h₁ := d.indexed S' j h
      rw [Array.getElem?_push]; split
      · subst_vars; simp at h₁
      · exact h₁
  good := by
    intro i pk c acc j h
    obtain ⟨S₀, h₁, h₂, h₃⟩ := d.good i pk c acc j h
    refine ⟨S₀, ?_, h₂, ?_⟩
    · rw [Array.getElem?_push]; split
      · subst_vars; simp at h₁
      · exact h₁
    · rw [Array.getElem?_push]; split
      · subst_vars; simp at h₃
      · exact h₃

/-- `d'` has every set of `d`, at the same number. -/
def Extends (d d' : Cache N m) : Prop := ∀ (i : Nat) (S : List Nat), d.states[i]? = some S → d'.states[i]? = some S

theorem push_extends (d : Cache N m) (S : List Nat) : Extends d (d.push S) := by
  unfold Extends; intro i S₀ h
  show (d.states.push S)[i]? = some S₀
  rw [Array.getElem?_push]; split
  · subst_vars; simp at h
  · exact h

/-- The number of the set `S`, adding it if it is new. -/
def intern (d : Cache N m) (S : List Nat) : Cache N m × Nat :=
  match d.index[S]? with
  | some j => (d, j)
  | none => (d.push S, d.states.size)

theorem intern_spec (d : Cache N m) (S : List Nat) :
    Extends d (d.intern S).1 ∧ (d.intern S).1.states[(d.intern S).2]? = some S := by
  unfold intern
  split
  · rename_i j h; exact ⟨fun _ _ h => h, d.indexed S j h⟩
  · exact ⟨push_extends d S, by simp [push]⟩

/-- Record a step that is `run`'s. -/
def record (d : Cache N m) (i pk : Nat) (c : Char) (j : Nat) (S : List Nat)
    (hi : d.states[i]? = some S) (hj : d.states[j]? = some (N.nextFast m (pk + N.ncode c) c S)) : Cache N m where
  states := d.states
  index := d.index
  indexed := d.indexed
  trans := d.trans.insert (i, pk, c) (S.any (N.nulAt (pk + N.ncode c)), j)
  good := by
    intro i' pk' c' acc j' h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk
      simp only [beq_iff_eq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨S, hi, rfl, hj⟩
    · exact d.good i' pk' c' acc j' h

/-- The step from set `i` (`S`) by `c`, computed and recorded. -/
@[specialize]
def advance (d : Cache N m) (i pk : Nat) (c : Char) (S : List Nat) (hS : d.states[i]? = some S) :
    Cache N m × Nat :=
  let S' := N.nextFast m (pk + N.ncode c) c S
  let hs := d.intern_spec S'
  ((d.intern S').1.record i pk c (d.intern S').2 S (hs.1 _ _ hS) hs.2, (d.intern S').2)

theorem advance_spec (d : Cache N m) (i pk : Nat) (c : Char) (S : List Nat)
    (hS : d.states[i]? = some S) :
    (d.advance i pk c S hS).1.states[(d.advance i pk c S hS).2]? = some (N.nextFast m (pk + N.ncode c) c S) :=
  (d.intern_spec _).2

end Cache

/-- `run`, through the cache. -/
@[specialize]
def crun (d : Cache N m) (i : Nat) (p : Option Char) : List Char → Bool
  | [] => (d.states[i]?.getD []).any (N.finAt (N.pcode p))
  | c :: cs =>
    let pk := N.pcode p
    match d.trans[(i, pk, c)]? with
    | some (acc, j) => if !m.anchorEnd && acc then true else crun d j (some c) cs
    | none =>
      match hS : d.states[i]? with
      | none => false
      | some S =>
        let k := pk + N.ncode c
        if !m.anchorEnd && S.any (N.nulAt k) then true
        else if d.states.size < maxStates then
          let a := d.advance i pk c S hS
          crun a.1 a.2 (some c) cs
        else N.run m (some c) cs (N.nextFast m k c S)

theorem crun_eq : ∀ (cs : List Char) (d : Cache N m) (i : Nat) (p : Option Char) (S : List Nat),
    d.states[i]? = some S → N.crun m d i p cs = N.run m p cs S
  | [], d, i, p, S, h => by simp [crun, run, h]
  | c :: cs, d, i, p, S, h => by
    unfold crun
    simp only
    split
    · rename_i acc j hc
      obtain ⟨S₀, h₀, hacc, hj⟩ := d.good _ _ _ _ _ hc
      rw [h] at h₀; cases h₀
      simp only [run, ← hacc]
      split
      · rfl
      · exact crun_eq cs d j (some c) _ hj
    · split
      · rename_i hS; rw [h] at hS; cases hS
      · rename_i S₁ hS
        have e : S₁ = S := by rw [h] at hS; cases hS; rfl
        subst e
        simp only [run]
        split
        · rfl
        · split
          · exact crun_eq cs _ _ (some c) _ (Cache.advance_spec d i (N.pcode p) c S₁ hS)
          · rfl

/-- Below this length a text runs `run` directly: too short for the
cache's bookkeeping to pay. -/
def cacheFrom : Nat := 256

/-- Whether the pattern matches `t` where the mode allows: the scan over
term numbers, through the cache on longer texts. -/
@[specialize]
def accepts (t : List Char) : Bool :=
  if t.length ≤ cacheFrom then N.run m none t [0]
  else N.crun m (Cache.start [0]) 0 none t

theorem accepts_run (t : List Char) : N.accepts m t = N.run m none t [0] := by
  unfold accepts
  split
  · rfl
  · exact N.crun_eq m t _ 0 none _ rfl

end Nfa

/-! ## Compiling a pattern -/

variable [Hashable κ]

/-- Every context slot of the masks. -/
def combos (mp mn : Side) : List (Side × Side) := (List.range (mp.size * mn.size)).map (unslot mp mn)

theorem mem_combos (mp mn pc nc : Side) : unslot mp mn (slot mp mn pc nc) ∈ combos mp mn :=
  List.mem_map.2 ⟨_, List.mem_range.2 (slot_lt mp mn pc nc), rfl⟩

/-- Number `q`, adding it if it is new. -/
@[specialize]
def intern (st : Array (Regex κ) × Std.HashMap (Regex κ) Nat) (q : Regex κ) : Array (Regex κ) × Std.HashMap (Regex κ) Nat :=
  if st.2.contains q then st else (st.1.push q, st.2.insert q st.1.size)

/-- No assertion read before the first character: then the context never
matters (`$` is no exception, as the tables know when the text has ended). -/
@[specialize]
def ctxFree (r : Regex κ) : Bool := within .nothing .nothing r

omit [CharClass κ] [DecidableEq κ] [Hashable κ] in
theorem nullB_ctxFree (pc nc pc' nc' : Side) (hn : nc.isEnd = nc'.isEnd) (r : Regex κ) (h : ctxFree r = true) :
    nullB pc nc r = nullB pc' nc' r :=
  nullB_agree (mp := .nothing) (mn := .nothing) (pc := pc) (pc' := pc') (nc := nc) (nc' := nc') rfl rfl hn r h

omit [CharClass κ] [Hashable κ] in
theorem lin_ctxFree (pc nc : Side) (hn : nc.isEnd = false) (r : Regex κ) (h : ctxFree r = true) :
    lin pc nc r = lin .nothing .nothing r :=
  lin_agree (mp := .nothing) (mn := .nothing) (pc := pc) (pc' := .nothing) (nc := nc) (nc' := .nothing) rfl rfl hn r h

/-- The slots whose linear forms can differ: those of the term's own masks,
one when the context never matters. -/
@[specialize]
def slots (t : Regex κ) : List (Side × Side) := combos (reads t).1 (reads t).2

/-- The pattern and its partial derivatives `PD r` (at most one per character
class), numbered, the pattern first. Every derivative of a numbered term is
numbered, since `PD` is closed under derivation (`PD_closed`); `build` checks
it in any case. No search, so nothing to bound. -/
@[specialize]
def numberTerms (r : Regex κ) : Array (Regex κ) × Std.HashMap (Regex κ) Nat :=
  (PD r).foldl intern (#[r], (∅ : Std.HashMap (Regex κ) Nat).insert r 0)

/-- The pattern's masks: every bit some term reads. -/
@[specialize]
def masks (terms : Array (Regex κ)) : Side × Side :=
  terms.foldl (fun m t => (m.1.union (reads t).1, m.2.union (reads t).2)) (.nothing, .nothing)

/-- A linear form with the derivatives as numbers. -/
@[specialize]
def numbered (idx : Std.HashMap (Regex κ) Nat) (l : List (κ × Regex κ)) : Array (κ × Nat) :=
  (l.map fun kq => (kq.1, idx.getD kq.2 0)).toArray

/-- Spread a term's row over its own slots (`local`, masks `tp`, `tn`) to
the pattern's slots (masks `mp`, `mn`): each pattern slot shares the entry of
the term slot it projects to. -/
@[inline] def spread {β : Type} (mp mn tp tn : Side) (d : β) (row : Array β) : Array β :=
  (Array.range (mp.size * mn.size)).map fun k => row.getD (slot tp tn (unslot mp mn k).1 (unslot mp mn k).2) d

theorem spread_get {β : Type} (mp mn tp tn : Side) (d : β) (row : Array β) (pc nc : Side) :
    (spread mp mn tp tn d row)[slot mp mn pc nc]? = some (row.getD (slot tp tn (mp.proj pc) (mn.proj nc)) d) := by
  simp [spread, slot_lt, unslot_slot]

/-- A term's table row: its linear form in each slot, with the derivatives
as numbers, computed once per slot of the term's own masks (once in all
when the context never matters). -/
@[specialize]
def transRow (mp mn : Side) (idx : Std.HashMap (Regex κ) Nat) (t : Regex κ) : Array (Array (κ × Nat)) :=
  if ctxFree t then
    let e := numbered idx (lin .nothing .nothing t)
    (Array.range (mp.size * mn.size)).map fun _ => e
  else
    let tp := (reads t).1
    let tn := (reads t).2
    spread mp mn tp tn #[] ((Array.range (tp.size * tn.size)).map fun k =>
      numbered idx (lin (unslot tp tn k).1 (unslot tp tn k).2 t))

/-- What `build` checks of each term's masks: they say what the term reads,
and the pattern's masks cover them. -/
def masksOk (mp mn : Side) (t : Regex κ) : Bool :=
  within (reads t).1 (reads t).2 t && (reads t).1.le mp && (reads t).2.le mn

omit [CharClass κ] [DecidableEq κ] [Hashable κ] in
theorem masksOk_spec {mp mn : Side} {t : Regex κ} (h : masksOk mp mn t = true) :
    within (reads t).1 (reads t).2 t = true ∧ (reads t).1.le mp = true ∧ (reads t).2.le mn = true := by
  simpa [masksOk, Bool.and_eq_true, and_assoc] using h

omit [CharClass κ] in
theorem transRow_get {mp mn : Side} (idx : Std.HashMap (Regex κ) Nat) {t : Regex κ} (ht : masksOk mp mn t = true)
    (pc nc : Side) (hn : nc.isEnd = false) :
    (transRow mp mn idx t)[slot mp mn pc nc]? = some (numbered idx (lin pc nc t)) := by
  obtain ⟨hw, hp, hq⟩ := masksOk_spec ht
  unfold transRow
  split
  · rename_i hf; simp [slot_lt, lin_ctxFree pc nc hn t hf]
  · have hn' : (mn.proj nc).isEnd = false := by simp [Side.proj, hn]
    rw [spread_get, Array.getD_eq_getD_getElem?]
    simp [slot_lt, lin_unslot hn' hw, lin_proj hw hp hq pc nc hn]

/-- A term's nullability before a character, in each slot. -/
@[specialize]
def nulRow (mp mn : Side) (t : Regex κ) : Array Bool :=
  if ctxFree t then
    let b := nullB .nothing .nothing t
    (Array.range (mp.size * mn.size)).map fun _ => b
  else
    let tp := (reads t).1
    let tn := (reads t).2
    spread mp mn tp tn false ((Array.range (tp.size * tn.size)).map fun k => nullB (unslot tp tn k).1 (unslot tp tn k).2 t)

omit [CharClass κ] [DecidableEq κ] [Hashable κ] in
theorem nulRow_get {mp mn : Side} {t : Regex κ} (ht : masksOk mp mn t = true) (pc nc : Side) (hn : nc.isEnd = false) :
    (nulRow mp mn t)[slot mp mn pc nc]? = some (nullB pc nc t) := by
  obtain ⟨hw, hp, hq⟩ := masksOk_spec ht
  unfold nulRow
  split
  · rename_i hf; simp [slot_lt, nullB_ctxFree pc nc .nothing .nothing hn t hf]
  · have hn' : (mn.proj nc).isEnd = false := by simp [Side.proj, hn]
    rw [spread_get, Array.getD_eq_getD_getElem?]
    simp [slot_lt, nullB_unslot hn' hw, nullB_proj hw hp hq pc nc hn]

/-- A term's nullability at the end, after a character in each slot. -/
@[specialize]
def finRow (mp : Side) (t : Regex κ) : Array Bool :=
  if ctxFree t then
    let b := nullB .nothing .atEnd t
    (Array.range mp.size).map fun _ => b
  else
    let tp := (reads t).1
    let row := (Array.range tp.size).map fun k => nullB (decode tp k) .atEnd t
    (Array.range mp.size).map fun k => row.getD (code tp (decode mp k)) false

omit [CharClass κ] [DecidableEq κ] [Hashable κ] in
theorem finRow_get {mp mn : Side} {t : Regex κ} (ht : masksOk mp mn t = true) (pc : Side) :
    (finRow mp t)[code mp pc]? = some (nullB pc .atEnd t) := by
  obtain ⟨hw, hp, -⟩ := masksOk_spec ht
  have hk := code_lt mp pc
  unfold finRow
  split
  · rename_i hf; simp [hk, nullB_ctxFree pc .atEnd .nothing .atEnd rfl t hf]
  · simp only [Array.getElem?_map, Array.getElem?_range, hk, ↓reduceIte, Option.map_some, Option.some.injEq,
      Array.getD_eq_getD_getElem?, decode_code, code_lt, Option.getD_some]
    rw [Side.proj_proj_of_le hp]
    exact nullB_agree (Side.proj_proj _ _) rfl rfl t hw

/-- Every derivative of `t` was numbered, and its number stands for it; and
its masks are right. -/
@[specialize]
def checkTerm (mp mn : Side) (terms : Array (Regex κ)) (idx : Std.HashMap (Regex κ) Nat) (t : Regex κ) : Bool :=
  masksOk mp mn t &&
    (slots t).all fun pn => (lin pn.1 pn.2 t).all fun kq => decide (terms[idx.getD kq.2 0]? = some kq.2)

omit [CharClass κ] in
theorem checkTerm_spec {mp mn : Side} {terms : Array (Regex κ)} {idx : Std.HashMap (Regex κ) Nat} {t : Regex κ}
    (h : checkTerm mp mn terms idx t = true) (pc nc : Side) (hn : nc.isEnd = false) :
    ∀ kq ∈ lin pc nc t, terms[idx.getD kq.2 0]? = some kq.2 := by
  intro kq hkq
  unfold checkTerm slots at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hm, h⟩ := h
  rw [← lin_unslot hn (masksOk_spec hm).1] at hkq
  have h1 := List.all_eq_true.1 h _ (mem_combos _ _ pc nc)
  have h2 := List.all_eq_true.1 h1 kq hkq
  simpa using h2

theorem range8_get {k : Nat} (h : k < 8) : (Array.range 8)[k]? = some k := by
  simp [h]

/-- Compile `r`: number its derivative terms, find the bits its assertions
read, and fill the tables, checking the numbering (`none` if it were
incomplete, and then the plain scan runs). -/
@[specialize]
def Nfa.build (r : Regex κ) : Option (Nfa r) :=
  let st := numberTerms r
  let terms := st.1
  let idx := st.2
  let mp := (masks terms).1
  let mn := (masks terms).2
  if h0 : terms[0]? = some r then
    if hc : terms.all (checkTerm mp mn terms idx) = true then
      have hchk : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → checkTerm mp mn terms idx t = true := by
        intro j t ht
        have hj : j < terms.size := by
          rcases Nat.lt_or_ge j terms.size with h | h
          · exact h
          · simp [Array.getElem?_eq_none h] at ht
        have htj : terms[j] = t := by simpa [hj] using ht
        have := (Array.all_eq_true.1 hc) j hj
        rwa [htj] at this
      have hw : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → masksOk mp mn t = true := fun j t ht => by
        have := hchk j t ht
        unfold checkTerm at this
        exact (Bool.and_eq_true _ _ ▸ this).1
      some {
        terms, mp, mn
        trans := terms.map (transRow mp mn idx), nul := terms.map (nulRow mp mn), fin := terms.map (finRow mp)
        start := h0
        hTrans := by
          intro j t ht pc nc hn
          simp only [Array.getElem?_map, ht, Option.map_some, Option.bind_some, transRow_get idx (hw j t ht) pc nc hn,
            Option.getD_some, numbered, List.toList_toArray, List.map_map]
          apply List.map_congr_left
          intro kq hkq
          simp only [Function.comp]
          rw [checkTerm_spec (hchk j t ht) pc nc hn kq hkq]
        hNul := by
          intro j t ht pc nc hn
          simp [Array.getElem?_map, ht, nulRow_get (hw j t ht) pc nc hn]
        hFin := by
          intro j t ht pc
          simp [Array.getElem?_map, ht, finRow_get (hw j t ht) pc]
        pcodes := (Array.range 128).map fun k => code mp (ctx κ (some (Char.ofNat k)))
        ncodes := (Array.range 128).map fun k => mp.size * code mn (ctx κ (some (Char.ofNat k)))
        hP := by
          intro k v h
          simp only [Array.getElem?_map, Array.getElem?_range] at h
          split at h <;> simp_all
        hN := by
          intro k v h
          simp only [Array.getElem?_map, Array.getElem?_range] at h
          split at h <;> simp_all }
    else none
  else none

end Regex

end Keel
