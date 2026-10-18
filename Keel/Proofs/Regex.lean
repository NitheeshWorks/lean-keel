import Keel.RepoImpl.RegexNfa

/-!
# Proofs: the laws of `Keel.Regex`

* `nullable_iff`: `nullable` decides the empty match, assertions included.
* `derive_correct`: the partial derivatives by `c` are exactly the ways to
  finish a match that starts with `c` (Antimirov's theorem, in context).
* `accepts_iff`: the scan decides `Accepts`, in every mode.
* `Nfa.accepts_eq`: the compiled matcher is the scan.
* `reach_length_le`: every state of the scan has at most `leaves r + 1`
  terms, so the work per character is bounded by the pattern and the scan is
  linear in the text. No input makes it backtrack.
-/

namespace Keel.Regex

variable {κ : Type} [CharClass κ] [DecidableEq κ] {r s : Regex κ} {p n : Option Char}

/-! ## Inversion -/

omit [DecidableEq κ] in
theorem matches_empty_iff {u : List Char} : Matches (empty : Regex κ) p u n ↔ False :=
  ⟨fun h => (by cases h), False.elim⟩

omit [DecidableEq κ] in
theorem matches_eps_iff {u : List Char} : Matches (eps : Regex κ) p u n ↔ u = [] :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .eps⟩

omit [DecidableEq κ] in
theorem matches_cls_iff {k : κ} {u : List Char} :
    Matches (cls k) p u n ↔ ∃ c, u = [c] ∧ CharClass.test k c = true :=
  ⟨fun h => by cases h with | cls h => exact ⟨_, rfl, h⟩, fun ⟨_, h, hc⟩ => h ▸ .cls hc⟩

omit [DecidableEq κ] in
theorem matches_assert_iff {a : Assertion} {u : List Char} :
    Matches (assert a : Regex κ) p u n ↔ u = [] ∧ a.holds (CharClass.word κ) p n = true :=
  ⟨fun h => by cases h with | assert h => exact ⟨rfl, h⟩, fun ⟨h, ha⟩ => h ▸ .assert ha⟩

omit [DecidableEq κ] in
theorem matches_alt_iff {u : List Char} :
    Matches (alt r s) p u n ↔ Matches r p u n ∨ Matches s p u n :=
  ⟨fun h => by cases h with | altL h => exact .inl h | altR h => exact .inr h,
   fun h => h.elim .altL .altR⟩

omit [DecidableEq κ] in
theorem matches_cat_iff {w : List Char} :
    Matches (cat r s) p w n ↔
      ∃ u v, w = u ++ v ∧ Matches r p u (v.head?.or n) ∧ Matches s (u.getLast?.or p) v n :=
  ⟨fun h => by cases h with | cat h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩,
   fun ⟨_, _, hw, h₁, h₂⟩ => hw ▸ .cat h₁ h₂⟩

omit [DecidableEq κ] in
theorem matches_star_iff {w : List Char} :
    Matches (star r) p w n ↔ w = [] ∨
      ∃ u v, u ≠ [] ∧ w = u ++ v ∧ Matches r p u (v.head?.or n) ∧
        Matches (star r) (u.getLast?.or p) v n := by
  constructor
  · intro h
    cases h with
    | starNil => exact .inl rfl
    | starCons hu h₁ h₂ => exact .inr ⟨_, _, hu, rfl, h₁, h₂⟩
  · rintro (h | ⟨_, _, hu, hw, h₁, h₂⟩)
    · exact h ▸ .starNil
    · exact hw ▸ .starCons hu h₁ h₂

theorem matches_seq_iff {w : List Char} : Matches (seq r s) p w n ↔ Matches (cat r s) p w n := by
  unfold seq
  split
  · subst_vars
    rw [matches_cat_iff]
    constructor
    · intro h; exact ⟨[], w, rfl, .eps, h⟩
    · rintro ⟨u, v, rfl, h₁, h₂⟩
      rw [matches_eps_iff] at h₁
      subst h₁
      exact h₂
  · exact Iff.rfl

theorem getLast?_or_cons (c : Char) (l : List Char) (p : Option Char) :
    (c :: l).getLast?.or p = l.getLast?.or (some c) := by
  cases l <;> simp [List.getLast?_cons]

/-! ## The empty match -/

omit [DecidableEq κ] in
/-- `nullable` decides whether `r` matches the empty string in context. -/
theorem nullable_iff (r : Regex κ) (p n : Option Char) : nullable p n r = true ↔ Matches r p [] n := by
  induction r with
  | empty => simp [nullable, matches_empty_iff]
  | eps => simp [nullable, matches_eps_iff]
  | cls k => simp [nullable, matches_cls_iff]
  | assert a => simp [nullable, matches_assert_iff]
  | alt r s ihr ihs => simp [nullable, matches_alt_iff, ihr, ihs]
  | cat r s ihr ihs =>
    simp only [nullable, Bool.and_eq_true, ihr, ihs, matches_cat_iff]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨[], [], rfl, h₁, h₂⟩
    · rintro ⟨u, v, huv, h₁, h₂⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv.symm
      exact ⟨h₁, h₂⟩
  | star r => simp [nullable, Matches.starNil]

/-! ## Partial derivatives -/

/-- **Antimirov's theorem, in context**: `r` matches `c :: u` after `p`
exactly when one of its partial derivatives by `c` matches `u` after `c`. -/
theorem derive_correct (p : Option Char) (c : Char) (r : Regex κ) (u : List Char) (n : Option Char) :
    Matches r p (c :: u) n ↔ ∃ q ∈ pd p c r, Matches q (some c) u n := by
  induction r generalizing u n with
  | empty => simp [pd, matches_empty_iff]
  | eps => simp [pd, matches_eps_iff]
  | assert a => simp [pd, matches_assert_iff]
  | cls k =>
    rw [matches_cls_iff]
    by_cases hk : CharClass.test k c = true
    · simp only [pd, hk, ite_true, List.mem_singleton, exists_eq_left, matches_eps_iff]
      constructor
      · rintro ⟨d, hd, _⟩
        simp only [List.cons.injEq] at hd
        exact hd.2
      · intro h; exact ⟨c, by simp [h], hk⟩
    · constructor
      · rintro ⟨d, hd, hdk⟩
        simp only [List.cons.injEq] at hd
        exact absurd (hd.1 ▸ hdk) hk
      · rintro ⟨q, hq, _⟩
        simp [pd, hk] at hq
  | alt r s ihr ihs =>
    simp only [matches_alt_iff, ihr, ihs, pd, List.mem_append]
    constructor
    · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩)
      · exact ⟨q, .inl hq, h⟩
      · exact ⟨q, .inr hq, h⟩
    · rintro ⟨q, hq | hq, h⟩
      · exact .inl ⟨q, hq, h⟩
      · exact .inr ⟨q, hq, h⟩
  | cat r s ihr ihs =>
    rw [matches_cat_iff]
    simp only [pd, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨u₁, v, hw, h₁, h₂⟩
      cases u₁ with
      | nil =>
        simp only [List.nil_append] at hw
        subst hw
        have hn : nullable p (some c) r = true := (nullable_iff r p (some c)).2 h₁
        obtain ⟨q, hq, hm⟩ := (ihs u n).1 h₂
        exact ⟨q, .inr (by simpa [hn] using hq), hm⟩
      | cons d u₁ =>
        simp only [List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨q, hq, hm⟩ := (ihr u₁ _).1 h₁
        refine ⟨seq q s, .inl ⟨q, hq, rfl⟩, ?_⟩
        rw [matches_seq_iff, matches_cat_iff]
        exact ⟨u₁, v, rfl, hm, by rwa [getLast?_or_cons] at h₂⟩
    · rintro ⟨q', h | h, hm⟩
      · obtain ⟨q, hq, rfl⟩ := h
        rw [matches_seq_iff, matches_cat_iff] at hm
        obtain ⟨u₁, v, rfl, h₁, h₂⟩ := hm
        exact ⟨c :: u₁, v, rfl, (ihr u₁ _).2 ⟨q, hq, h₁⟩, by rwa [getLast?_or_cons]⟩
      · split at h
        · rename_i hn
          exact ⟨[], c :: u, rfl, (nullable_iff r p (some c)).1 hn, (ihs u n).2 ⟨q', h, hm⟩⟩
        · simp at h
  | star r ih =>
    rw [matches_star_iff]
    simp only [pd, List.mem_map]
    constructor
    · rintro (h | ⟨u₁, v, hne, hw, h₁, h₂⟩)
      · simp at h
      · cases u₁ with
        | nil => exact absurd rfl hne
        | cons d u₁ =>
          simp only [List.cons_append, List.cons.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          obtain ⟨q, hq, hm⟩ := (ih u₁ _).1 h₁
          refine ⟨seq q (star r), ⟨q, hq, rfl⟩, ?_⟩
          rw [matches_seq_iff, matches_cat_iff]
          exact ⟨u₁, v, rfl, hm, by rwa [getLast?_or_cons] at h₂⟩
    · rintro ⟨q', ⟨q, hq, rfl⟩, hm⟩
      rw [matches_seq_iff, matches_cat_iff] at hm
      obtain ⟨u₁, v, rfl, h₁, h₂⟩ := hm
      exact .inr ⟨c :: u₁, v, List.cons_ne_nil _ _, rfl, (ih u₁ _).2 ⟨q, hq, h₁⟩,
        by rwa [getLast?_or_cons]⟩

/-! ## The scan -/

omit [CharClass κ] in
theorem mem_foldl_insert (l acc : List (Regex κ)) (q : Regex κ) :
    q ∈ l.foldl (fun acc q => acc.insert q) acc ↔ q ∈ acc ∨ q ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, List.mem_insert_iff, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h

omit [CharClass κ] in
theorem nodup_insert {l : List (Regex κ)} (q : Regex κ) (h : l.Nodup) : (l.insert q).Nodup := by
  unfold List.insert
  split
  · exact h
  · rename_i hq
    exact List.nodup_cons.2 ⟨by simpa using hq, h⟩

omit [CharClass κ] in
theorem nodup_foldl_insert (l acc : List (Regex κ)) (h : acc.Nodup) :
    (l.foldl (fun acc q => acc.insert q) acc).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons a l ih => exact ih _ (nodup_insert a h)

theorem mem_next {m : Mode} {r q : Regex κ} {c : Char} {T : List (Regex κ)} :
    q ∈ next m r p c T ↔ (m.anchorStart = false ∧ q = r) ∨ ∃ t ∈ T, q ∈ pd p c t := by
  unfold next
  cases m.anchorStart <;> simp [uniq, List.mem_insert_iff, mem_foldl_insert, List.mem_flatMap]

/-! ## The compiled matcher is the scan -/

namespace Nfa

variable {r : Regex κ} (N : Nfa r) (m : Mode)

/-- The terms the numbers in `S` stand for. -/
def Den (S : List Nat) (T : List (Regex κ)) : Prop := ∀ q, q ∈ T ↔ ∃ j ∈ S, N.terms[j]? = some q

omit [CharClass κ] in
theorem some_of_lt {j : Nat} (h : j < N.terms.size) : ∃ t, N.terms[j]? = some t :=
  ⟨N.terms[j], by simp [h]⟩

omit [CharClass κ] in
theorem lt_of_some {j : Nat} {t : Regex κ} (h : N.terms[j]? = some t) : j < N.terms.size := by
  rcases Nat.lt_or_ge j N.terms.size with h' | h'
  · exact h'
  · simp [Array.getElem?_eq_none h'] at h

theorem any_nul {S : List Nat} {T : List (Regex κ)} (hd : N.Den S T) (p : Option Char) (c : Char) :
    S.any (N.nulAt (N.pcode p + N.ncode c)) = T.any (nullable p (some c)) := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hn⟩
    unfold nulAt at hn
    split at hn
    · rename_i hlt
      obtain ⟨t, ht⟩ := N.some_of_lt hlt
      rw [getD2, N.slot_eq, N.hNul j t ht _ _ (ctx_some_isEnd κ c)] at hn
      exact ⟨t, (hd t).2 ⟨j, hj, ht⟩, by rw [nullable_eq]; exact hn⟩
    · cases hn
  · rintro ⟨q, hq, hn⟩
    obtain ⟨j, hj, ht⟩ := (hd q).1 hq
    refine ⟨j, hj, ?_⟩
    unfold nulAt
    simp only [N.lt_of_some ht, ↓reduceIte]; rw [getD2, N.slot_eq, N.hNul j q ht _ _ (ctx_some_isEnd κ c)]
    rw [nullable_eq] at hn; exact hn

theorem any_fin {S : List Nat} {T : List (Regex κ)} (hd : N.Den S T) (p : Option Char) :
    S.any (N.finAt (N.pcode p)) = T.any (nullable p none) := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hn⟩
    unfold finAt at hn
    split at hn
    · rename_i hlt
      obtain ⟨t, ht⟩ := N.some_of_lt hlt
      rw [getD2, pcode, N.hFin j t ht] at hn
      exact ⟨t, (hd t).2 ⟨j, hj, ht⟩, by rw [nullable_eq, ctx_none]; exact hn⟩
    · cases hn
  · rintro ⟨q, hq, hn⟩
    obtain ⟨j, hj, ht⟩ := (hd q).1 hq
    refine ⟨j, hj, ?_⟩
    unfold finAt
    simp only [N.lt_of_some ht, ↓reduceIte]; rw [getD2, pcode, N.hFin j q ht]
    rw [nullable_eq, ctx_none] at hn; exact hn

/-- One term's numbered derivatives stand for its partial derivatives. -/
theorem edges_den {j : Nat} {t : Regex κ} (ht : N.terms[j]? = some t) (p : Option Char) (c : Char) (q : Regex κ) :
    (∃ e ∈ (N.edges j (N.pcode p + N.ncode c)).toList, CharClass.test e.1 c = true ∧ N.terms[e.2]? = some q) ↔
      q ∈ pd p c t := by
  rw [pd_eq_lin, pick, List.mem_filterMap]
  have hm := N.hTrans j t ht (ctx κ p) (ctx κ (some c)) (ctx_some_isEnd κ c)
  rw [← N.slot_eq] at hm
  constructor
  · rintro ⟨e, he, hc, hq⟩
    have : (e.1, some q) ∈ (lin (ctx κ p) (ctx κ (some c)) t).map (fun kq => (kq.1, some kq.2)) := by
      rw [← hm, List.mem_map]; exact ⟨e, by rw [← N.edges_eq]; exact he, by rw [hq]⟩
    obtain ⟨kq, hkq, he'⟩ := List.mem_map.1 this
    simp only [Prod.mk.injEq, Option.some.injEq] at he'
    exact ⟨kq, hkq, by rw [he'.1, hc, he'.2]; rfl⟩
  · rintro ⟨kq, hkq, hc⟩
    split at hc
    · rename_i htest
      simp only [Option.some.injEq] at hc
      have : (kq.1, some kq.2) ∈ ((N.edges j (N.pcode p + N.ncode c)).toList).map (fun e => (e.1, N.terms[e.2]?)) := by
        rw [N.edges_eq, hm, List.mem_map]; exact ⟨kq, hkq, rfl⟩
      obtain ⟨e, he, he'⟩ := List.mem_map.1 this
      simp only [Prod.mk.injEq] at he'
      exact ⟨e, he, by rw [he'.1]; exact htest, by rw [he'.2, hc]⟩
    · cases hc

theorem next_den {S : List Nat} {T : List (Regex κ)} (hd : N.Den S T) (p : Option Char) (c : Char) :
    N.Den (N.next m (N.pcode p + N.ncode c) c S) (Regex.next m r p c T) := by
  intro q
  rw [mem_next]
  simp only [Nfa.next, mem_dedupIds, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (⟨ha, rfl⟩ | ⟨t, ht, hq⟩)
    · exact ⟨0, .inl (by simp [restart, ha]), N.start⟩
    · obtain ⟨j, hj, hjt⟩ := (hd t).1 ht
      obtain ⟨e, he, hc, hq'⟩ := (N.edges_den hjt p c q).2 hq
      refine ⟨e.2, .inr ⟨j, hj, ?_⟩, hq'⟩
      simp only [N.lt_of_some hjt, ↓reduceIte]; rw [List.mem_filterMap]
      exact ⟨e, he, by simp [hc]⟩
  · rintro ⟨i, (hi | ⟨j, hj, hi⟩), hq⟩
    · unfold restart at hi
      split at hi
      · simp at hi
      · rename_i ha
        simp only [List.mem_singleton] at hi; subst hi
        rw [N.start] at hq
        exact .inl ⟨by simpa using ha, (Option.some.inj hq).symm⟩
    · right
      split at hi
      · rename_i hlt
        obtain ⟨t, ht⟩ := N.some_of_lt hlt
        rw [List.mem_filterMap] at hi
        obtain ⟨e, he, hei⟩ := hi
        split at hei
        · rename_i hc
          simp only [Option.some.injEq] at hei; subst hei
          exact ⟨t, (hd t).2 ⟨j, hj, ht⟩, (N.edges_den ht p c q).1 ⟨e, he, hc, hq⟩⟩
        · cases hei
      · cases hi

theorem run_eq : ∀ (cs : List Char) (p : Option Char) (S : List Nat) (T : List (Regex κ)),
    N.Den S T → N.run m p cs S = scan m r p cs T
  | [], p, S, T, hd => by simp only [run, scan]; exact N.any_fin hd p
  | c :: cs, p, S, T, hd => by
    simp only [run, scan, N.any_nul hd p c]
    split
    · rfl
    · exact run_eq cs (some c) _ _ (fun q => by
        rw [N.next_den m hd p c q]; simp only [N.nextFast_mem])

/-- **The compiled matcher is the scan.** -/
theorem accepts_eq (t : List Char) : N.accepts m t = r.accepts m t := by
  rw [N.accepts_run]; unfold Regex.accepts
  apply N.run_eq
  intro q
  simp only [List.mem_singleton, exists_eq_left]
  constructor
  · rintro rfl; exact N.start
  · intro h; rw [N.start] at h; exact (Option.some.inj h).symm

end Nfa

/-- What the scan's state means after the text `pre`: a term of it matches
`v` exactly when `r` matches from a position in `pre` (the start, if the mode
anchors it) through `v`. -/
def Inv (m : Mode) (r : Regex κ) (pre : List Char) (T : List (Regex κ)) : Prop :=
  ∀ v n, (∃ q ∈ T, Matches q pre.getLast? v n) ↔
    ∃ u₁ u₂, pre = u₁ ++ u₂ ∧ (m.anchorStart = true → u₁ = []) ∧ Matches r u₁.getLast? (u₂ ++ v) n

omit [DecidableEq κ] in
theorem inv_init (m : Mode) (r : Regex κ) : Inv m r [] [r] := by
  intro v n
  constructor
  · rintro ⟨q, hq, h⟩
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨[], [], rfl, fun _ => rfl, h⟩
  · rintro ⟨u₁, u₂, h, -, hm⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h.symm
    exact ⟨r, List.mem_singleton_self r, hm⟩

theorem inv_next {m : Mode} {r : Regex κ} {pre : List Char} {T : List (Regex κ)} (c : Char)
    (h : Inv m r pre T) : Inv m r (pre ++ [c]) (next m r pre.getLast? c T) := by
  intro v n
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  have step : (∃ q ∈ next m r pre.getLast? c T, Matches q (some c) v n) ↔
      (m.anchorStart = false ∧ Matches r (some c) v n) ∨
        ∃ u₁ u₂, pre = u₁ ++ u₂ ∧ (m.anchorStart = true → u₁ = []) ∧
          Matches r u₁.getLast? (u₂ ++ c :: v) n := by
    rw [← h (c :: v) n]
    simp only [mem_next]
    constructor
    · rintro ⟨q, ⟨ha, rfl⟩ | ⟨t, ht, hq⟩, hm⟩
      · exact .inl ⟨ha, hm⟩
      · exact .inr ⟨t, ht, (derive_correct _ c t v n).2 ⟨q, hq, hm⟩⟩
    · rintro (⟨ha, hm⟩ | ⟨t, ht, hm⟩)
      · exact ⟨r, .inl ⟨ha, rfl⟩, hm⟩
      · obtain ⟨q, hq, hm⟩ := (derive_correct _ c t v n).1 hm
        exact ⟨q, .inr ⟨t, ht, hq⟩, hm⟩
  rw [step]
  constructor
  · rintro (⟨ha, hm⟩ | ⟨u₁, u₂, rfl, hs, hm⟩)
    · exact ⟨pre ++ [c], [], by simp, by simp [ha], by simpa using hm⟩
    · exact ⟨u₁, u₂ ++ [c], by simp, hs, by simpa using hm⟩
  · rintro ⟨u₁, u₂, hpre, hs, hm⟩
    rcases List.eq_nil_or_concat u₂ with rfl | ⟨L, b, rfl⟩
    · simp only [List.append_nil] at hpre
      subst hpre
      refine .inl ⟨?_, by simpa using hm⟩
      cases ha : m.anchorStart
      · rfl
      · exact absurd (hs ha) (by simp)
    · simp only [List.concat_eq_append, ← List.append_assoc] at hpre
      obtain ⟨rfl, hcb⟩ := List.append_inj' hpre rfl
      simp only [List.cons.injEq, and_true] at hcb
      subst hcb
      exact .inr ⟨u₁, L, rfl, hs, by simpa using hm⟩

theorem scan_spec (m : Mode) (r : Regex κ) (rest : List Char) :
    ∀ (pre : List Char) (T : List (Regex κ)), Inv m r pre T →
      (scan m r pre.getLast? rest T = true ↔
        ∃ x y, rest = x ++ y ∧ (m.anchorEnd = true → y = []) ∧ ∃ u₁ u₂, pre ++ x = u₁ ++ u₂ ∧
          (m.anchorStart = true → u₁ = []) ∧ Matches r u₁.getLast? u₂ y.head?) := by
  induction rest with
  | nil =>
    intro pre T h
    simp only [scan, List.any_eq_true, nullable_iff]
    rw [show (∃ q ∈ T, Matches q pre.getLast? [] none) ↔ _ from h [] none]
    constructor
    · rintro ⟨u₁, u₂, hpre, hs, hm⟩
      exact ⟨[], [], rfl, fun _ => rfl, u₁, u₂, by simpa using hpre, hs, by simpa using hm⟩
    · rintro ⟨x, y, hxy, -, u₁, u₂, hpre, hs, hm⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hxy.symm
      exact ⟨u₁, u₂, by simpa using hpre, hs, by simpa using hm⟩
  | cons c cs ih =>
    intro pre T h
    have ih' := ih (pre ++ [c]) _ (inv_next c h)
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at ih'
    have first : (T.any (nullable pre.getLast? (some c)) = true) ↔
        ∃ u₁ u₂, pre = u₁ ++ u₂ ∧ (m.anchorStart = true → u₁ = []) ∧
          Matches r u₁.getLast? u₂ (some c) := by
      simp only [List.any_eq_true, nullable_iff]
      rw [show (∃ q ∈ T, Matches q pre.getLast? [] (some c)) ↔ _ from h [] (some c)]
      simp
    have hscan : scan m r pre.getLast? (c :: cs) T = true ↔
        (m.anchorEnd = false ∧ T.any (nullable pre.getLast? (some c)) = true) ∨
          scan m r (some c) cs (next m r pre.getLast? c T) = true := by
      simp only [scan]
      cases m.anchorEnd <;> split <;> simp_all
    rw [hscan, first, ih']
    constructor
    · rintro (⟨he, u₁, u₂, hpre, hs, hm⟩ | ⟨x, y, rfl, hy, u₁, u₂, hpre, hs, hm⟩)
      · exact ⟨[], c :: cs, rfl, by simp [he], u₁, u₂, by simpa using hpre, hs, hm⟩
      · exact ⟨c :: x, y, rfl, hy, u₁, u₂, by simpa using hpre, hs, hm⟩
    · rintro ⟨x, y, hxy, hy, u₁, u₂, hpre, hs, hm⟩
      cases x with
      | nil =>
        simp only [List.nil_append] at hxy
        subst hxy
        refine .inl ⟨?_, u₁, u₂, by simpa using hpre, hs, hm⟩
        cases he : m.anchorEnd
        · rfl
        · exact absurd (hy he) (by simp)
      | cons d x =>
        simp only [List.cons_append, List.cons.injEq] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        exact .inr ⟨x, y, rfl, hy, u₁, u₂, by simpa using hpre, hs, hm⟩

/-- **The matcher decides acceptance**: `r.accepts m t` holds exactly when
`r` matches a segment of `t` that the mode allows, with the assertions read
in context. -/
theorem accepts_iff (m : Mode) (r : Regex κ) (t : List Char) : r.accepts m t = true ↔ Accepts m r t := by
  unfold accepts Accepts
  rw [show (none : Option Char) = ([] : List Char).getLast? from rfl,
    scan_spec m r t [] [r] (inv_init m r)]
  simp

/-! ## The state is bounded by the pattern -/

theorem pd_mem_PD {p : Option Char} {c : Char} {q : Regex κ} :
    ∀ {r : Regex κ}, q ∈ pd p c r → q ∈ PD r
  | empty, h | eps, h | assert _, h => by simp [pd] at h
  | cls k, h => by
    simp only [pd] at h
    split at h <;> simp_all [PD]
  | alt r s, h => by
    simp only [pd, List.mem_append] at h
    simp only [PD, List.mem_append]
    exact h.imp pd_mem_PD pd_mem_PD
  | cat r s, h => by
    simp only [pd, List.mem_append, List.mem_map] at h
    simp only [PD, List.mem_append, List.mem_map]
    rcases h with ⟨q', hq', rfl⟩ | h
    · exact .inl ⟨q', pd_mem_PD hq', rfl⟩
    · split at h
      · exact .inr (pd_mem_PD h)
      · simp at h
  | star r, h => by
    simp only [pd, List.mem_map] at h
    simp only [PD, List.mem_map]
    obtain ⟨q', hq', rfl⟩ := h
    exact ⟨q', pd_mem_PD hq', rfl⟩

/-- **The partial derivatives are closed under derivation** (Antimirov). -/
theorem PD_closed {p : Option Char} {c : Char} :
    ∀ {r q q' : Regex κ}, q ∈ PD r → q' ∈ pd p c q → q' ∈ PD r
  | empty, _, _, h, _ | eps, _, _, h, _ | assert _, _, _, h, _ => by simp [PD] at h
  | cls k, q, q', h, h' => by
    simp only [PD, List.mem_singleton] at h
    subst h
    simp [pd] at h'
  | alt r s, q, q', h, h' => by
    simp only [PD, List.mem_append] at h ⊢
    exact h.imp (PD_closed · h') (PD_closed · h')
  | cat r s, q, q', h, h' => by
    simp only [PD, List.mem_append, List.mem_map] at h ⊢
    rcases h with ⟨q₁, hq₁, rfl⟩ | h
    · unfold seq at h'
      split at h'
      · exact .inr (pd_mem_PD h')
      · simp only [pd, List.mem_append, List.mem_map] at h'
        rcases h' with ⟨q₂, hq₂, rfl⟩ | h'
        · exact .inl ⟨q₂, PD_closed hq₁ hq₂, rfl⟩
        · split at h'
          · exact .inr (pd_mem_PD h')
          · simp at h'
    · exact .inr (PD_closed h h')
  | star r, q, q', h, h' => by
    simp only [PD, List.mem_map] at h
    obtain ⟨q₁, hq₁, rfl⟩ := h
    have hstar : ∀ {x}, x ∈ pd p c (star r) → x ∈ PD (star r) := pd_mem_PD
    unfold seq at h'
    split at h'
    · exact hstar h'
    · simp only [pd, List.mem_append, List.mem_map] at h'
      rcases h' with ⟨q₂, hq₂, rfl⟩ | h'
      · simp only [PD, List.mem_map]
        exact ⟨q₂, PD_closed hq₁ hq₂, rfl⟩
      · split at h'
        · exact hstar h'
        · simp at h'

omit [CharClass κ] in
theorem length_PD : ∀ r : Regex κ, (PD r).length = r.leaves
  | empty | eps | assert _ | cls _ => rfl
  | alt r s | cat r s => by simp [PD, leaves, length_PD r, length_PD s]
  | star r => by simp [PD, leaves, length_PD r]

omit [CharClass κ] in
theorem reach_init (r : Regex κ) : Reach r [r] :=
  ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun q hq => by simp_all⟩

theorem reach_next {m : Mode} {r : Regex κ} {T : List (Regex κ)} (p : Option Char) (c : Char)
    (h : Reach r T) : Reach r (next m r p c T) := by
  refine ⟨?_, fun q hq => ?_⟩
  · unfold next; split
    · exact nodup_foldl_insert _ [] List.nodup_nil
    · exact nodup_insert r (nodup_foldl_insert _ [] List.nodup_nil)
  rcases mem_next.1 hq with ⟨-, rfl⟩ | ⟨t, ht, hqt⟩
  · exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ ?_
    rcases List.mem_cons.1 (h.2 t ht) with htr | htp
    · exact pd_mem_PD (htr ▸ hqt)
    · exact PD_closed htp hqt

omit [CharClass κ] in
/-- **The scan's state is bounded by the pattern**: a reachable state has at
most one term per character class of `r`, plus `r`. -/
theorem reach_length_le {r : Regex κ} {T : List (Regex κ)} (h : Reach r T) : T.length ≤ r.leaves + 1 := by
  have := List.Nodup.length_le_of_subset h.1 (fun q hq => h.2 q hq)
  simpa [length_PD] using this

end Keel.Regex
