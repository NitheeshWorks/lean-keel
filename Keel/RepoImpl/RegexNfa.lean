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
slot is a pair of the context classes that can occur, as far as the
pattern's assertions tell them apart (`classes`), and each term's linear
form is computed once for every slot (`linS`). Matching
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

The tables of a pattern have a row per context its terms can tell apart. A
context is a pair of sides; what the pattern reads of a side is its
projection on the pattern's masks (`masks`, from `reads`), and the sides a
position can have are few (`sideCands`: an end of the text, each ASCII
character's, a non-ASCII word or non-word character's). So a side's class
is one of the distinct projections (`classes`), at most six for a dialect
whose `\n` and `\r` are not word characters, whatever assertions the
pattern uses, and a slot is a pair of classes. -/

/-- A non-ASCII word character's side. -/
def Side.wordChar : Side := ⟨false, true, false, false, false⟩

/-- A non-ASCII non-word character's side. -/
def Side.otherChar : Side := ⟨false, false, false, false, false⟩

/-- The sides a position can have. -/
def sideCands (κ : Type) [CharClass κ] : List Side :=
  .atEnd :: .wordChar :: .otherChar :: (List.range 128).map fun k => ctx κ (some (Char.ofNat k))

theorem asciiWord_of_ge {c : Char} (h : 128 ≤ c.toNat) : asciiWord c = false := by
  have hv : 128 ≤ c.val.toNat := h
  simp [asciiWord, Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit]
  refine ⟨⟨⟨fun _ => ?_, fun _ => ?_⟩, fun _ => ?_⟩, ?_⟩
  all_goals first
    | (rw [UInt32.lt_iff_toNat_lt]; simp; omega)
    | (rintro rfl; simp at h)

/-- A non-ASCII character's side: its word bit, and nothing else. -/
theorem ctx_of_ge (κ : Type) [CharClass κ] {c : Char} (h : 128 ≤ c.toNat) :
    ctx κ (some c) = if CharClass.word κ c then .wordChar else .otherChar := by
  have hl : (some c == some '\n') = false := by simp; rintro rfl; simp at h
  have hr : (some c == some '\r') = false := by simp; rintro rfl; simp at h
  simp only [ctx, Option.isNone_some, wordAt, asciiWord_of_ge h, hl, hr]
  split <;> simp_all [Side.wordChar, Side.otherChar]

theorem ctx_mem_sideCands (κ : Type) [CharClass κ] (p : Option Char) : ctx κ p ∈ sideCands κ := by
  match p with
  | none => exact List.mem_cons_self
  | some c =>
    by_cases h : c.toNat < 128
    · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))
      exact List.mem_map.2 ⟨c.toNat, List.mem_range.2 h, by rw [Char.ofNat_toNat]⟩
    · rw [ctx_of_ge κ (by omega)]
      split
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The classes of the sides under a mask: their distinct projections. -/
def classes (m : Side) (l : List Side) : List Side := (l.map m.proj).eraseDups

theorem proj_mem_classes {m s : Side} {l : List Side} (h : s ∈ l) : m.proj s ∈ classes m l :=
  List.mem_eraseDups.2 (List.mem_map.2 ⟨s, h, rfl⟩)

/-- A side's class number. -/
def code (cls : List Side) (s : Side) : Nat := cls.idxOf s

/-- The side of a class number. -/
def decode (cls : List Side) (k : Nat) : Side := cls.getD k .nothing

theorem decode_classes_isEnd {m : Side} (hm : m.isEnd = false) {l : List Side} (k : Nat) :
    (decode (classes m l) k).isEnd = false := by
  unfold decode
  rw [List.getD_eq_getElem?_getD]
  cases h : (classes m l)[k]? with
  | none => rfl
  | some x =>
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 (List.mem_eraseDups.1 (List.mem_of_getElem? h))
    simp [Side.proj, hm]

theorem code_lt {cls : List Side} {s : Side} (h : s ∈ cls) : code cls s < cls.length :=
  List.idxOf_lt_length_iff.2 h

theorem decode_code {cls : List Side} {s : Side} (h : s ∈ cls) : decode cls (code cls s) = s := by
  have hl := List.idxOf_lt_length_iff.2 h
  simp only [decode, code, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hl, Option.getD_some, List.getElem_idxOf]

/-- A character's slot part: from a table for ASCII characters, else the
part of a non-ASCII word or non-word character (or of the end). -/
@[inline] def codeOf (κ : Type) [CharClass κ] (tab : Array Nat) (w o e : Nat) : Option Char → Nat
  | some c => if h : c.toNat < tab.size then tab[c.toNat] else if CharClass.word κ c then w else o
  | none => e

/-- The table of a side function on the ASCII characters. -/
def table (κ : Type) [CharClass κ] (f : Side → Nat) : Array Nat :=
  (Array.range 128).map fun k => f (ctx κ (some (Char.ofNat k)))

theorem codeOf_table (κ : Type) [CharClass κ] (f : Side → Nat) (p : Option Char) :
    codeOf κ (table κ f) (f .wordChar) (f .otherChar) (f .atEnd) p = f (ctx κ p) := by
  match p with
  | none => rfl
  | some c =>
    simp only [codeOf, table, Array.size_map, Array.size_range, Array.getElem_map, Array.getElem_range]
    split
    · rw [Char.ofNat_toNat]
    · rw [ctx_of_ge κ (by omega)]; split <;> rfl

/-! ### Slot sets and the linear form over every slot at once -/

/-- The slots below `K` where `f` holds, as a bit set. -/
def bitsBelow (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | K + 1 => bitsBelow f K ||| (if f K then 1 <<< K else 0)

theorem testBit_bitsBelow (f : Nat → Bool) (k : Nat) : ∀ K, (bitsBelow f K).testBit k = (decide (k < K) && f k)
  | 0 => by simp [bitsBelow]
  | K + 1 => by
    simp only [bitsBelow, Nat.testBit_or, testBit_bitsBelow f k K]
    by_cases hk : k < K
    · have : K ≠ k := by omega
      split <;> simp [hk, Nat.shiftLeft_eq, this, show k < K + 1 by omega]
    · by_cases he : k = K
      · subst he; split <;> simp_all [Nat.shiftLeft_eq]
      · have : K ≠ k := Ne.symm he
        split <;> simp [hk, Nat.shiftLeft_eq, this, show ¬ k < K + 1 by omega]

/-- The context slots of a table: `K` of them with their contexts `cx`;
every slot as a bit set (`all`), and the slots where each assertion holds
(`aset`), computed once per pattern. -/
structure Slots where
  cx : Nat → Side × Side
  K : Nat
  all : Nat
  aset : Assertion → Nat
  hall : ∀ k, all.testBit k = decide (k < K)
  haset : ∀ a k, (aset a).testBit k = (decide (k < K) && a.holdsB (cx k).1 (cx k).2)

/-- Every assertion, in constructor order. -/
def allAssertions : Array Assertion :=
  #[.start, .finish, .wordBoundary, .notWordBoundary, .wordStart, .wordEnd, .lineStart, .lineEnd,
    .lineStartCRLF, .lineEndCRLF, .wordBoundaryAscii, .notWordBoundaryAscii, .wordStartAscii,
    .wordEndAscii, .wordStartHalf, .wordEndHalf, .wordStartHalfAscii, .wordEndHalfAscii]

theorem allAssertions_get (a : Assertion) : allAssertions[a.ctorIdx]? = some a := by
  cases a <;> rfl

/-- The slots of `K` contexts, with each assertion's set computed once. -/
def Slots.of (cx : Nat → Side × Side) (K : Nat) : Slots :=
  let sets := allAssertions.map fun a => bitsBelow (fun k => a.holdsB (cx k).1 (cx k).2) K
  { cx, K, all := bitsBelow (fun _ => true) K, aset := fun a => sets.getD a.ctorIdx 0
    hall := fun k => by simp [testBit_bitsBelow]
    haset := fun a k => by
      simp only [sets, Array.getD_eq_getD_getElem?, Array.getElem?_map, allAssertions_get, Option.map_some,
        Option.getD_some, testBit_bitsBelow] }

/-- The slots where `r` is nullable. -/
def nullSet (S : Slots) : Regex κ → Nat
  | empty | cls _ => 0
  | eps | star _ => S.all
  | assert a => S.aset a
  | alt r s => nullSet S r ||| nullSet S s
  | cat r s => nullSet S r &&& nullSet S s

omit [CharClass κ] [DecidableEq κ] in
theorem testBit_nullSet (S : Slots) {k : Nat} (hk : k < S.K) :
    ∀ r : Regex κ, (nullSet S r).testBit k = nullB (S.cx k).1 (S.cx k).2 r
  | empty | cls _ => by simp [nullSet, nullB]
  | eps | star _ => by simp [nullSet, nullB, S.hall, hk]
  | assert a => by simp [nullSet, nullB, S.haset, hk]
  | alt r s => by simp [nullSet, nullB, Nat.testBit_or, testBit_nullSet S hk r, testBit_nullSet S hk s]
  | cat r s => by simp [nullSet, nullB, Nat.testBit_and, testBit_nullSet S hk r, testBit_nullSet S hk s]

/-- The linear form in every slot at once: each derivative with its class
and the set of slots (within `g`) where the linear form has it. -/
@[specialize]
def linS (S : Slots) (g : Nat) : Regex κ → List (κ × Regex κ × Nat)
  | cls k => [(k, eps, g)]
  | alt r s => linS S g r ++ linS S g s
  | cat r s =>
    (linS S g r).map (fun e => (e.1, seq e.2.1 s, e.2.2)) ++
      (let g' := g &&& nullSet S r
       if g' = 0 then [] else linS S g' s)
  | star r => (linS S g r).map (fun e => (e.1, seq e.2.1 (star r), e.2.2))
  | _ => []

/-- The entries of a slot-tagged list in slot `k`. -/
def atSlot {β : Type} (k : Nat) (l : List (κ × β × Nat)) : List (κ × β) :=
  l.filterMap fun e => if e.2.2.testBit k then some (e.1, e.2.1) else none

omit [CharClass κ] [DecidableEq κ] in
theorem atSlot_map {β γ : Type} (k : Nat) (f : β → γ) (l : List (κ × β × Nat)) :
    atSlot k (l.map fun e => (e.1, f e.2.1, e.2.2)) = (atSlot k l).map fun kq => (kq.1, f kq.2) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [atSlot] at ih ⊢
    simp only [List.map_cons, List.filterMap_cons]
    by_cases hb : e.2.2.testBit k <;> simp [hb, ih]

omit [CharClass κ] [DecidableEq κ] in
theorem atSlot_append {β : Type} (k : Nat) (l l' : List (κ × β × Nat)) :
    atSlot k (l ++ l') = atSlot k l ++ atSlot k l' := List.filterMap_append

omit [CharClass κ] in
/-- **The tagged linear form is the linear form in each slot.** -/
theorem atSlot_linS (S : Slots) {k : Nat} (hk : k < S.K) : ∀ (g : Nat) (r : Regex κ),
      atSlot k (linS S g r) = if g.testBit k then lin (S.cx k).1 (S.cx k).2 r else []
  | g, empty | g, eps | g, assert _ => by simp [linS, atSlot, lin]
  | g, cls c => by by_cases hb : g.testBit k <;> simp [linS, atSlot, lin, hb]
  | g, alt r s => by
    rw [linS, lin, atSlot_append, atSlot_linS S hk g r, atSlot_linS S hk g s]
    split <;> simp
  | g, cat r s => by
    have hb : (g &&& nullSet S r).testBit k = (g.testBit k && nullB (S.cx k).1 (S.cx k).2 r) := by
      rw [Nat.testBit_and, testBit_nullSet S hk r]
    have hm := atSlot_map k (fun q => seq q s) (linS S g r)
    rw [linS, lin, atSlot_append, hm, atSlot_linS S hk g r]
    simp only
    by_cases h0 : (g &&& nullSet S r) = 0
    · simp only [h0, ↓reduceIte]
      rw [h0, Nat.zero_testBit] at hb
      cases hg : g.testBit k <;> cases hn : nullB (S.cx k).1 (S.cx k).2 r <;> simp_all [atSlot]
    · simp only [h0, ↓reduceIte]
      rw [atSlot_linS S hk _ s, hb]
      cases g.testBit k <;> cases nullB (S.cx k).1 (S.cx k).2 r <;> simp
  | g, star r => by
    have hm := atSlot_map k (fun q => seq q (star r)) (linS S g r)
    rw [linS, lin, hm, atSlot_linS S hk g r]
    split <;> simp

/-- `f` on each `k < K`, computed once per value of `key`. -/
def memoRow {α β : Type} [DecidableEq α] (key : Nat → α) (f : Nat → β) (K : Nat) : Array β :=
  ((List.range K).foldl (fun (acc : Array β × List (α × β)) k =>
    match acc.2.find? (fun e => decide (e.1 = key k)) with
    | some e => (acc.1.push e.2, acc.2)
    | none => let b := f k; (acc.1.push b, (key k, b) :: acc.2)) (#[], [])).1

theorem memoRow_get {α β : Type} [DecidableEq α] (key : Nat → α) (f : Nat → β) (K : Nat)
    (hf : ∀ k k', k < K → k' < K → key k = key k' → f k = f k') {k : Nat} (hk : k < K) :
    (memoRow key f K)[k]? = some (f k) := by
  -- the fold keeps: the row is `f` on the slots so far, and each memo entry is `f` at a slot so far
  let Inv (n : Nat) (acc : Array β × List (α × β)) : Prop :=
    acc.1.size = n ∧ (∀ i (h : i < acc.1.size), acc.1[i] = f i) ∧ ∀ e ∈ acc.2, ∃ i < n, key i = e.1 ∧ e.2 = f i
  have step : ∀ n, n ≤ K → ∀ acc, Inv 0 acc → Inv n ((List.range n).foldl (fun (acc : Array β × List (α × β)) k =>
      match acc.2.find? (fun e => decide (e.1 = key k)) with
      | some e => (acc.1.push e.2, acc.2)
      | none => let b := f k; (acc.1.push b, (key k, b) :: acc.2)) acc) := by
    intro n
    induction n with
    | zero => intro _ acc h; exact h
    | succ n ih =>
      intro hn acc h0
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hs, hv, hm⟩ := ih (by omega) acc h0
      generalize List.foldl _ acc (List.range n) = acc' at hs hv hm
      split
      · rename_i e he
        obtain ⟨i, hi, hki, hei⟩ := hm e (List.mem_of_find?_eq_some he)
        have hke : e.1 = key n := by simpa using List.find?_some he
        refine ⟨by simp [hs], fun j hj => ?_, fun e' he' => ?_⟩
        · rw [Array.getElem_push]; split
          · exact hv j _
          · have : j = n := by simp at hj; omega
            subst this; rw [hei]; exact hf i j (by omega) (by omega) (hki.trans hke)
        · obtain ⟨i', hi', h'⟩ := hm e' he'; exact ⟨i', by omega, h'⟩
      · refine ⟨by simp [hs], fun j hj => ?_, fun e' he' => ?_⟩
        · rw [Array.getElem_push]; split
          · exact hv j _
          · have : j = n := by simp at hj; omega
            subst this; rfl
        · rcases List.mem_cons.1 he' with rfl | he'
          · exact ⟨n, by omega, rfl, rfl⟩
          · obtain ⟨i', hi', h'⟩ := hm e' he'; exact ⟨i', by omega, h'⟩
  obtain ⟨hs, hv, -⟩ := step K (Nat.le_refl K) (#[], []) ⟨rfl, fun i h => by simp at h, fun e he => by simp at he⟩
  unfold memoRow
  rw [Array.getElem?_eq_getElem (by omega), hv]

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
the pattern); for each term and context slot, its linear form with the
derivatives as numbers, and whether it is nullable before a character and
at the end; and the tables that give a character's slot part. The fields
after the tables say they are right, for every context a text can give. -/
structure Nfa (r : Regex κ) where
  terms : Array (Regex κ)
  trans : Array (Array (Array (κ × Nat)))
  nul : Array (Array Bool)
  fin : Array (Array Bool)
  /-- The slot part of each ASCII character as the character before. -/
  pcodes : Array Nat
  /-- The slot parts of a non-ASCII word and non-word character before, and of the start. -/
  pW : Nat
  pN : Nat
  pE : Nat
  /-- The slot part of each ASCII character as the character read. -/
  ncodes : Array Nat
  /-- The slot parts of a non-ASCII word and non-word character read. -/
  nW : Nat
  nN : Nat
  start : terms[0]? = some r
  hTrans : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → ∀ (p : Option Char) (c : Char),
    ((trans[j]?.bind (·[codeOf κ pcodes pW pN pE p + codeOf κ ncodes nW nN 0 (some c)]?)).getD #[]).toList.map
        (fun e => (e.1, terms[e.2]?)) =
      (lin (ctx κ p) (ctx κ (some c)) t).map (fun kq => (kq.1, some kq.2))
  hNul : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → ∀ (p : Option Char) (c : Char),
    (nul[j]?.bind (·[codeOf κ pcodes pW pN pE p + codeOf κ ncodes nW nN 0 (some c)]?)).getD false =
      nullB (ctx κ p) (ctx κ (some c)) t
  hFin : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → ∀ (p : Option Char),
    (fin[j]?.bind (·[codeOf κ pcodes pW pN pE p]?)).getD false = nullB (ctx κ p) .atEnd t

namespace Nfa

variable {r : Regex κ} (N : Nfa r) (m : Mode)

/-- The term numbers a step adds for a match starting after the character
read: the pattern's, unless the start is anchored. -/
def restart : List Nat := if m.anchorStart then [] else [0]

/-- The slot part of the character before. -/
@[inline] def pcode (p : Option Char) : Nat := codeOf κ N.pcodes N.pW N.pN N.pE p

/-- The slot part of the character read. -/
@[inline] def ncode (c : Char) : Nat := codeOf κ N.ncodes N.nW N.nN 0 (some c)

theorem trans_eq {j : Nat} {t : Regex κ} (ht : N.terms[j]? = some t) (p : Option Char) (c : Char) :
    ((N.trans[j]?.bind (·[N.pcode p + N.ncode c]?)).getD #[]).toList.map (fun e => (e.1, N.terms[e.2]?)) =
      (lin (ctx κ p) (ctx κ (some c)) t).map (fun kq => (kq.1, some kq.2)) := N.hTrans j t ht p c

theorem nul_eq {j : Nat} {t : Regex κ} (ht : N.terms[j]? = some t) (p : Option Char) (c : Char) :
    (N.nul[j]?.bind (·[N.pcode p + N.ncode c]?)).getD false = nullB (ctx κ p) (ctx κ (some c)) t :=
  N.hNul j t ht p c

theorem fin_eq {j : Nat} {t : Regex κ} (ht : N.terms[j]? = some t) (p : Option Char) :
    (N.fin[j]?.bind (·[N.pcode p]?)).getD false = nullB (ctx κ p) .atEnd t := N.hFin j t ht p

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

/-- The context slots of the classes: before (`pcls`) and after (`ncls`). -/
def combos (pcls ncls : List Side) : List (Side × Side) :=
  (List.range (pcls.length * ncls.length)).map fun k => (decode pcls (k % pcls.length), decode ncls (k / pcls.length))

/-- The number of context slots of the classes. -/
def slots (pcls ncls : List Side) : Nat := pcls.length * ncls.length

theorem mem_combos {pcls ncls : List Side} {k : Nat} (hk : k < slots pcls ncls) :
    (decode pcls (k % pcls.length), decode ncls (k / pcls.length)) ∈ combos pcls ncls :=
  List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

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

/-- A term's table row: its linear form in each slot, with the derivatives
as numbers. The tagged linear form `ls` is computed and numbered once; a
slot's entry is those tagged with it, built once per projection of the slot
on the term's own masks and shared. -/
@[specialize]
def transRowOf (S : Slots) (idx : Std.HashMap (Regex κ) Nat) (t : Regex κ)
    (ls : List (κ × Regex κ × Nat)) : Array (Array (κ × Nat)) :=
  let es := ls.map fun e => (e.1, idx.getD e.2.1 0, e.2.2)
  memoRow (fun k => ((reads t).1.proj (S.cx k).1, (reads t).2.proj (S.cx k).2)) (fun k => (atSlot k es).toArray) S.K

/-- `transRowOf` on the term's tagged linear form. -/
@[specialize]
def transRow (S : Slots) (idx : Std.HashMap (Regex κ) Nat) (t : Regex κ) : Array (Array (κ × Nat)) :=
  transRowOf S idx t (linS S S.all t)

/-- What `build` checks of each term's masks: they say what the term reads,
and the pattern's masks cover them. -/
def masksOk (mp mn : Side) (t : Regex κ) : Bool :=
  within (reads t).1 (reads t).2 t && (reads t).1.le mp && (reads t).2.le mn

omit [CharClass κ] [DecidableEq κ] [Hashable κ] in
theorem masksOk_spec {mp mn : Side} {t : Regex κ} (h : masksOk mp mn t = true) :
    within (reads t).1 (reads t).2 t = true ∧ (reads t).1.le mp = true ∧ (reads t).2.le mn = true := by
  simpa [masksOk, Bool.and_eq_true, and_assoc] using h

omit [CharClass κ] in
theorem transRow_get (S : Slots) (idx : Std.HashMap (Regex κ) Nat) {t : Regex κ}
    (hw : within (reads t).1 (reads t).2 t = true) (hend : ∀ k, (S.cx k).2.isEnd = false) {k : Nat} (hk : k < S.K) :
    (transRow S idx t)[k]? = some (numbered idx (lin (S.cx k).1 (S.cx k).2 t)) := by
  have hm := fun k => atSlot_map k (fun q => idx.getD q 0) (linS S S.all t)
  unfold transRow transRowOf
  rw [memoRow_get _ _ _ ?_ hk]
  · rw [hm, atSlot_linS S hk]
    simp [S.hall k, hk, numbered]
  · intro k₁ k₂ h₁ h₂ he
    simp only [Prod.mk.injEq] at he
    rw [hm, hm, atSlot_linS S h₁, atSlot_linS S h₂, lin_agree he.1 he.2 (by rw [hend, hend]) t hw]
    simp [S.hall, h₁, h₂]

/-- A term's nullability before a character, in each slot. -/
@[specialize]
def nulRow (S : Slots) (t : Regex κ) : Array Bool :=
  if ctxFree t then
    let b := nullB .nothing .nothing t
    (Array.range S.K).map fun _ => b
  else
    let ns := nullSet S t
    (Array.range S.K).map fun k => ns.testBit k

omit [CharClass κ] [DecidableEq κ] [Hashable κ] in
theorem nulRow_get (S : Slots) {t : Regex κ} (hend : ∀ k, (S.cx k).2.isEnd = false) {k : Nat} (hk : k < S.K) :
    (nulRow S t)[k]? = some (nullB (S.cx k).1 (S.cx k).2 t) := by
  unfold nulRow
  split
  · rename_i hf; simp [hk, nullB_ctxFree (S.cx k).1 (S.cx k).2 .nothing .nothing (hend k) t hf]
  · simp [hk, testBit_nullSet S hk]

/-- A term's nullability at the end, after a character of each class (the
slots `F`, whose contexts are a class and the end). -/
@[specialize]
def finRow (F : Slots) (t : Regex κ) : Array Bool :=
  let ns := nullSet F t
  (Array.range F.K).map fun k => ns.testBit k

omit [CharClass κ] [DecidableEq κ] [Hashable κ] in
theorem finRow_get (F : Slots) {t : Regex κ} {k : Nat} (hk : k < F.K) :
    (finRow F t)[k]? = some (nullB (F.cx k).1 (F.cx k).2 t) := by
  unfold finRow
  simp [hk, testBit_nullSet F hk]

/-- Every derivative of `t` was numbered, and its number stands for it; and
its masks are right. -/
@[specialize]
def checkTermOf (mp mn : Side) (terms : Array (Regex κ)) (idx : Std.HashMap (Regex κ) Nat) (t : Regex κ)
    (ls : List (κ × Regex κ × Nat)) : Bool :=
  masksOk mp mn t && ls.all fun e => decide (terms[idx.getD e.2.1 0]? = some e.2.1)

/-- `checkTermOf` on the term's tagged linear form. -/
@[specialize]
def checkTerm (S : Slots) (mp mn : Side) (terms : Array (Regex κ))
    (idx : Std.HashMap (Regex κ) Nat) (t : Regex κ) : Bool :=
  checkTermOf mp mn terms idx t (linS S S.all t)

omit [CharClass κ] in
theorem checkTerm_spec (S : Slots) {mp mn : Side} {terms : Array (Regex κ)} {idx : Std.HashMap (Regex κ) Nat}
    {t : Regex κ} (h : checkTerm S mp mn terms idx t = true) {k : Nat} (hk : k < S.K) :
    ∀ kq ∈ lin (S.cx k).1 (S.cx k).2 t, terms[idx.getD kq.2 0]? = some kq.2 := by
  intro kq hkq
  unfold checkTerm checkTermOf at h
  rw [Bool.and_eq_true] at h
  have hs := atSlot_linS S hk S.all t
  simp only [S.hall k, hk, decide_true, ↓reduceIte] at hs
  rw [← hs, atSlot, List.mem_filterMap] at hkq
  obtain ⟨e, he, hkq⟩ := hkq
  split at hkq
  · simp only [Option.some.injEq] at hkq; subst hkq
    simpa using List.all_eq_true.1 h.2 e he
  · cases hkq

theorem range8_get {k : Nat} (h : k < 8) : (Array.range 8)[k]? = some k := by
  simp [h]

theorem slot_div_mod {P a b : Nat} (ha : a < P) : (a + P * b) % P = a ∧ (a + P * b) / P = b := by
  have hP : 0 < P := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt ha, Nat.zero_add]

theorem slot_lt {P Q a b : Nat} (ha : a < P) (hb : b < Q) : a + P * b < P * Q := by
  calc a + P * b < P + P * b := by omega
    _ = P * (b + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ ≤ P * Q := Nat.mul_le_mul_left _ hb

/-- Compile `r`: number its derivative terms, find the classes of context
its assertions tell apart, and fill the tables, checking the numbering
(`none` if it were incomplete, and then the plain scan runs). -/
@[specialize]
def Nfa.build (r : Regex κ) : Option (Nfa r) :=
  let st := numberTerms r
  let terms := st.1
  let idx := st.2
  let mp := (masks terms).1
  let mn := { (masks terms).2 with isEnd := false }
  let pcls := classes mp (sideCands κ)
  let ncls := classes mn (sideCands κ)
  let P := pcls.length
  let K := slots pcls ncls
  let S := Slots.of (fun k => (decode pcls (k % P), decode ncls (k / P))) K
  let F := Slots.of (fun k => (decode pcls k, .atEnd)) P
  let pf := fun s => code pcls (mp.proj s)
  let nf := fun s => P * code ncls (mn.proj s)
  if h0 : terms[0]? = some r then
    -- each term with its tagged linear form, computed once for the check and the row
    let forms := terms.map fun t => (t, linS S S.all t)
    if hc : forms.all (fun f => checkTermOf mp mn terms idx f.1 f.2) = true then
      have hchk : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → checkTerm S mp mn terms idx t = true := by
        intro j t ht
        have hj : j < terms.size := by
          rcases Nat.lt_or_ge j terms.size with h | h
          · exact h
          · simp [Array.getElem?_eq_none h] at ht
        have htj : terms[j] = t := by simpa [hj] using ht
        have := (Array.all_eq_true.1 hc) j (by simpa [forms] using hj)
        simp only [forms, Array.getElem_map, htj] at this
        exact this
      have hm : ∀ (j : Nat) (t : Regex κ), terms[j]? = some t → masksOk mp mn t = true := fun j t ht => by
        have := hchk j t ht
        unfold checkTerm checkTermOf at this
        exact (Bool.and_eq_true _ _ ▸ this).1
      have hpm : ∀ p, mp.proj (ctx κ p) ∈ pcls := fun p => proj_mem_classes (ctx_mem_sideCands κ p)
      have hnm : ∀ p, mn.proj (ctx κ p) ∈ ncls := fun p => proj_mem_classes (ctx_mem_sideCands κ p)
      -- a text's context lands on a slot whose context is its projection
      have hslot : ∀ (p : Option Char) (c : Char),
          codeOf κ (table κ pf) (pf .wordChar) (pf .otherChar) (pf .atEnd) p +
            codeOf κ (table κ nf) (nf .wordChar) (nf .otherChar) 0 (some c) < K ∧
          S.cx (codeOf κ (table κ pf) (pf .wordChar) (pf .otherChar) (pf .atEnd) p +
            codeOf κ (table κ nf) (nf .wordChar) (nf .otherChar) 0 (some c)) =
            (mp.proj (ctx κ p), mn.proj (ctx κ (some c))) := by
        intro p c
        rw [codeOf_table κ pf p, show codeOf κ (table κ nf) (nf .wordChar) (nf .otherChar) 0 (some c) =
          codeOf κ (table κ nf) (nf .wordChar) (nf .otherChar) (nf .atEnd) (some c) from rfl, codeOf_table κ nf]
        have ha := code_lt (hpm p)
        have hb := code_lt (hnm (some c))
        obtain ⟨h1, h2⟩ := slot_div_mod (P := P) (b := code ncls (mn.proj (ctx κ (some c)))) ha
        refine ⟨slot_lt ha hb, ?_⟩
        simp only [S, Slots.of, pf, nf, h1, h2, decode_code (hpm p), decode_code (hnm (some c))]
      have hend : ∀ k, (S.cx k).2.isEnd = false := fun k => decode_classes_isEnd rfl _
      some {
        terms
        trans := forms.map fun f => transRowOf S idx f.1 f.2, nul := terms.map (nulRow S), fin := terms.map (finRow F)
        pcodes := table κ pf, pW := pf .wordChar, pN := pf .otherChar, pE := pf .atEnd
        ncodes := table κ nf, nW := nf .wordChar, nN := nf .otherChar
        start := h0
        hTrans := by
          intro j t ht p c
          obtain ⟨hk, hcx⟩ := hslot p c
          obtain ⟨hw, hp, hq⟩ := masksOk_spec (hm j t ht)
          simp only [forms, Array.getElem?_map, ht, Option.map_some, Option.bind_some,
            show transRowOf S idx t (linS S S.all t) = transRow S idx t from rfl,
            transRow_get S idx hw hend hk, Option.getD_some, numbered, List.toList_toArray, List.map_map, hcx]
          rw [lin_proj hw hp hq _ _ (ctx_some_isEnd κ c)]
          apply List.map_congr_left
          intro kq hkq
          simp only [Function.comp]
          have := checkTerm_spec S (hchk j t ht) hk kq (by rw [hcx, lin_proj hw hp hq _ _ (ctx_some_isEnd κ c)]; exact hkq)
          rw [this]
        hNul := by
          intro j t ht p c
          obtain ⟨hk, hcx⟩ := hslot p c
          obtain ⟨hw, hp, hq⟩ := masksOk_spec (hm j t ht)
          simp [Array.getElem?_map, ht, nulRow_get S hend hk, hcx, nullB_proj hw hp hq _ _ (ctx_some_isEnd κ c)]
        hFin := by
          intro j t ht p
          obtain ⟨hw, hp, -⟩ := masksOk_spec (hm j t ht)
          have hk := code_lt (hpm p)
          rw [codeOf_table κ pf p]
          simp only [Array.getElem?_map, ht, Option.map_some, Option.bind_some]
          rw [finRow_get F (k := pf (ctx κ p)) hk, Option.getD_some]
          show nullB (decode pcls (code pcls (mp.proj (ctx κ p)))) .atEnd t = _
          rw [decode_code (hpm p)]
          exact nullB_agree (Side.proj_proj_of_le hp _) rfl rfl t hw }
    else none
  else none

end Regex

end Keel
