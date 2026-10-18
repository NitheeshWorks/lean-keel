import Keel.RepoImpl.Route

/-!
# Proofs: the laws of `Keel.Route`

* `match_urlFor`: an aligned template matches the URL it renders, giving back
  the values.
* `urlFor_match`: the URL of what a path matched is the path, when the path
  is in canonical form.
* `dispatch_found_iff`, `dispatch_partial_iff`, `dispatch_none_iff`: first
  match, and the three outcomes characterised.
* `resolve_found_iff`, `methodNotAllowed_iff` (405 exactly when some route
  matches the path, none matches the method too), `notFound_iff`.
-/

namespace Keel

namespace PathTemplate

/-! ## The search -/

theorem firstDown_eq {β : Type} (f : Nat → Option β) {m : Nat} {b : β} (hm : f m = some b) :
    ∀ n, m ≤ n → (∀ k, m < k → k ≤ n → f k = none) → firstDown f n = some b
  | 0, h0, _ => by
    have : m = 0 := by omega
    subst this; exact hm
  | n + 1, hle, hk => by
    simp only [firstDown]
    by_cases h : m = n + 1
    · subst h; rw [hm]
    · rw [hk (n + 1) (by omega) (Nat.le_refl _)]
      exact firstDown_eq f hm n (by omega) fun k h1 h2 => hk k h1 (by omega)

theorem firstDown_some {β : Type} {f : Nat → Option β} {b : β} :
    ∀ n, firstDown f n = some b → ∃ k ≤ n, f k = some b
  | 0, h => ⟨0, Nat.le_refl _, h⟩
  | n + 1, h => by
    simp only [firstDown] at h
    split at h
    · rename_i b' hb; cases h; exact ⟨n + 1, Nat.le_refl _, hb⟩
    · obtain ⟨k, hk, hf⟩ := firstDown_some n h
      exact ⟨k, by omega, hf⟩

/-! ## Soundness of the split -/

/-- The texts a split finds spell out the path, one per capture. -/
theorem split_sound : ∀ (ps : List Piece) (s : List Char) (ts : List (List Char)),
    split ps s = some ts → urlTexts ps ts = s
  | [], s, ts, h => by
    simp only [split] at h
    by_cases hs : s = []
    · simp only [hs, ite_true, Option.some.injEq] at h; subst h hs; rfl
    · simp [hs] at h
  | .lit l :: ps, s, ts, h => by
    simp only [split] at h
    by_cases hp : l <+: s
    · simp only [hp, ite_true] at h
      simp only [urlTexts, split_sound ps _ ts h]
      obtain ⟨r, rfl⟩ := hp
      simp
    · simp [hp] at h
  | .cap n c :: ps, s, ts, h => by
    simp only [split] at h
    obtain ⟨k, _, hk⟩ := firstDown_some _ h
    by_cases ha : c.accepts (s.take k) = true
    · simp only [ha, ite_true] at hk
      cases hsp : split ps (s.drop k) with
      | none => rw [hsp] at hk; cases hk
      | some ts' =>
        rw [hsp] at hk
        simp only [Option.map_some, Option.some.injEq] at hk
        subst hk
        simp [urlTexts, split_sound ps _ _ hsp]
    · simp [ha] at hk

/-! ## Completeness on aligned templates -/

theorem not_accepts_of_slash {c : Convertor} (hc : c.segment = true) {t : List Char}
    (h : '/' ∈ t) : c.accepts t = false := by
  cases ha : c.accepts t
  · rfl
  · exact absurd h (c.segment_spec hc t ha)

theorem aligned_tail_lit {l : List Char} {ps : List Piece} (h : aligned (.lit l :: ps) = true) :
    aligned ps = true := h

theorem aligned_tail_cap {n : String} {c : Convertor} {ps : List Piece}
    (h : aligned (.cap n c :: ps) = true) : aligned ps = true := by
  match ps, h with
  | [], _ => rfl
  | .lit l :: ps', h => simp only [aligned, Bool.and_eq_true] at h; exact h.2

/-- On an aligned template, the split of a rendered path is its texts. -/
theorem split_urlTexts : ∀ (ps : List Piece) (ts : List (List Char)), aligned ps = true →
    TextsAccepted ps ts → split ps (urlTexts ps ts) = some ts
  | [], ts, _, hacc => by simp only [TextsAccepted] at hacc; subst hacc; simp [split, urlTexts]
  | .lit l :: ps, ts, ha, hacc => by
    simp only [urlTexts, split, List.prefix_append, ite_true, List.drop_left]
    exact split_urlTexts ps ts (aligned_tail_lit ha) hacc
  | .cap n c :: ps, [], _, hacc => by simp [TextsAccepted] at hacc
  | .cap n c :: ps, t :: ts, ha, ⟨ht, hacc⟩ => by
    simp only [urlTexts, split]
    have hsplit := split_urlTexts ps ts (aligned_tail_cap ha) hacc
    apply firstDown_eq _ (m := t.length)
    · simp [ht, hsplit]
    · simp
    · intro k hk1 hk2
      simp only [List.length_append] at hk2
      match ps, ha, hk2, hacc with
      | [], _, hk2, hacc =>
        simp only [TextsAccepted] at hacc; subst hacc; simp [urlTexts] at hk2; omega
      | .lit l :: ps', ha, hk2, _ =>
        simp only [aligned, Bool.and_eq_true, beq_iff_eq] at ha
        obtain ⟨⟨hseg, hl⟩, _⟩ := ha
        obtain ⟨l', rfl⟩ : ∃ l', l = '/' :: l' := by
          cases l with
          | nil => simp at hl
          | cons x l' => simp at hl; exact ⟨l', by rw [hl]⟩
        have hslash : '/' ∈ (t ++ urlTexts (.lit ('/' :: l') :: ps') ts).take k := by
          rw [List.take_append, List.take_of_length_le (by omega)]
          simp only [urlTexts, List.cons_append]
          obtain ⟨j, hj⟩ : ∃ j, k - t.length = j + 1 := ⟨k - t.length - 1, by omega⟩
          rw [hj]; simp
        simp [not_accepts_of_slash hseg hslash]
      | .cap _ _ :: _, ha, _, _ => simp [aligned] at ha

theorem renderArgs_accepted : ∀ (ps : List Piece) (v : Args ps), ArgsValid ps v →
    TextsAccepted ps (renderArgs ps v)
  | [], _, _ => rfl
  | .lit _ :: ps, v, h => renderArgs_accepted ps v h
  | .cap _ c :: ps, (x, v), ⟨hx, hv⟩ => ⟨c.accepts_render x hx, renderArgs_accepted ps v hv⟩

theorem convert_renderArgs : ∀ (ps : List Piece) (v : Args ps), ArgsValid ps v →
    convert ps (renderArgs ps v) = some v
  | [], (), _ => rfl
  | .lit _ :: ps, v, h => convert_renderArgs ps v h
  | .cap _ c :: ps, (x, v), ⟨hx, hv⟩ => by
    show (match c.parse (c.render x), convert ps (renderArgs ps v) with
      | some x, some v => some (x, v) | _, _ => none) = some (x, v)
    rw [c.parse_render x hx, convert_renderArgs ps v hv]

/-- **`match` inverts `urlFor`**: an aligned template matches the URL it
renders for valid values, and gives the values back. -/
theorem match_urlFor (t : PathTemplate) (ha : t.Aligned) (v : Args t.pieces)
    (hv : ArgsValid t.pieces v) : t.match (t.urlFor v) = some v := by
  simp only [«match», urlFor, matchPieces, String.toList_ofList]
  rw [split_urlTexts _ _ ha (renderArgs_accepted _ v hv)]
  exact convert_renderArgs _ v hv

theorem renderArgs_convert : ∀ (ps : List Piece) (ts : List (List Char)) (v : Args ps),
    convert ps ts = some v → TextsCanonical ps ts → renderArgs ps v = ts
  | [], [], (), _, _ => rfl
  | [], _ :: _, _, h, _ => by simp [convert] at h
  | .lit _ :: ps, ts, v, h, hc => renderArgs_convert ps ts v h hc
  | .cap _ _ :: _, [], _, h, _ => by simp [convert] at h
  | .cap _ c :: ps, t :: ts, (x, v), h, ⟨hct, hc⟩ => by
    have h' : (match c.parse t, convert ps ts with
      | some x, some v => some (x, v) | _, _ => none) = some (x, v) := h
    cases hx : c.parse t with
    | none => rw [hx] at h'; cases h'
    | some x' =>
      cases hv : convert ps ts with
      | none => rw [hx, hv] at h'; cases h'
      | some v' =>
        rw [hx, hv] at h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        show c.render x' :: renderArgs ps v' = t :: ts
        rw [hct x' hx, renderArgs_convert ps ts v' hv hc]

/-- **`urlFor` inverts `match`** on canonical paths: the URL of the values a
path matched is the path, when its captured texts are in canonical form (no
leading zeros on an `int`, lower case in a `uuid`, …). -/
theorem urlFor_match (t : PathTemplate) {path : String} {v : Args t.pieces}
    (h : t.match path = some v) (hc : t.Canonical path) : t.urlFor v = path := by
  simp only [«match», matchPieces] at h
  cases hs : split t.pieces path.toList with
  | none => rw [hs] at h; cases h
  | some ts =>
    rw [hs] at h
    simp only [Option.bind_some] at h
    have := split_sound _ _ _ hs
    simp only [urlFor, renderArgs_convert _ ts v h (hc ts hs), this, String.ofList_toList]

end PathTemplate

/-! ## First-match dispatch -/

section Dispatch

universe u
variable {ρ : Type u} {β : ρ → Type} (m : (r : ρ) → Match (β r))

/-- Where `r` occurs in a list headed by `r₀`: at the head, or in the tail. -/
theorem exists_cons_split {α : Type u} (r₀ r : α) (rs : List α) (P : List α → Prop) :
    (∃ pre post, r₀ :: rs = pre ++ r :: post ∧ P pre) ↔
      (r₀ = r ∧ P []) ∨ ∃ pre post, rs = pre ++ r :: post ∧ P (r₀ :: pre) := by
  constructor
  · rintro ⟨pre, post, he, hp⟩
    cases pre with
    | nil => simp only [List.nil_append, List.cons.injEq] at he; exact Or.inl ⟨he.1, hp⟩
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact Or.inr ⟨pre, post, he, hp⟩
  · rintro (⟨rfl, hp⟩ | ⟨pre, post, he, hp⟩)
    · exact ⟨[], rs, rfl, hp⟩
    · exact ⟨r₀ :: pre, post, by simp [he], hp⟩

/-- **First match.** The dispatch finds `r` exactly when `r` matches fully and
no earlier route does. -/
theorem dispatch_found_iff : ∀ (rs : List ρ) (r : ρ) (b : β r),
    dispatch m rs = .found r b ↔
      ∃ pre post, rs = pre ++ r :: post ∧ m r = .full b ∧ ∀ r' ∈ pre, ¬ (m r').IsFull
  | [], r, b => by simp [dispatch]
  | r₀ :: rs, r, b => by
    have reorg : (∃ pre post, rs = pre ++ r :: post ∧ m r = .full b ∧ ∀ r' ∈ r₀ :: pre, ¬ (m r').IsFull) ↔
        ¬ (m r₀).IsFull ∧ dispatch m rs = .found r b := by
      rw [dispatch_found_iff rs r b]
      simp only [List.forall_mem_cons]
      constructor
      · rintro ⟨pre, post, h1, h2, h3, h4⟩; exact ⟨h3, pre, post, h1, h2, h4⟩
      · rintro ⟨h3, pre, post, h1, h2, h4⟩; exact ⟨pre, post, h1, h2, h3, h4⟩
    rw [exists_cons_split r₀ r rs fun pre => m r = .full b ∧ ∀ r' ∈ pre, ¬ (m r').IsFull, reorg]
    simp only [dispatch, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    cases hm : m r₀ with
    | full b₀ =>
      simp only [Match.IsFull, not_true_eq_false, false_and, or_false]
      constructor
      · intro h; cases h; exact ⟨rfl, hm⟩
      · rintro ⟨rfl, h⟩; rw [hm] at h; cases h; rfl
    | «partial» =>
      have : ¬ (r₀ = r ∧ m r = .full b) := by rintro ⟨rfl, h⟩; rw [hm] at h; cases h
      simp only [Match.IsFull, not_false_eq_true, true_and, this, false_or]
      cases dispatch m rs <;> simp
    | none =>
      have : ¬ (r₀ = r ∧ m r = .full b) := by rintro ⟨rfl, h⟩; rw [hm] at h; cases h
      simp only [Match.IsFull, not_false_eq_true, true_and, this, false_or]

theorem dispatch_found_full {rs : List ρ} {r : ρ} {b : β r} (h : dispatch m rs = .found r b) :
    ∃ r' ∈ rs, (m r').IsFull := by
  obtain ⟨pre, post, he, hr, _⟩ := (dispatch_found_iff m rs r b).1 h
  exact ⟨r, by simp [he], by rw [hr]; trivial⟩

/-- No route matches the path: dispatch finds nothing. -/
theorem dispatch_none_iff : ∀ rs : List ρ, dispatch m rs = .none ↔ ∀ r ∈ rs, m r = .none
  | [] => by simp [dispatch]
  | r :: rs => by
    have ih := dispatch_none_iff rs
    simp only [dispatch, List.mem_cons, forall_eq_or_imp]
    cases hm : m r with
    | full b => simp
    | «partial» => cases dispatch m rs <;> simp
    | none => simp [ih]

/-- **Partial iff no full match and some partial match.** -/
theorem dispatch_partial_iff : ∀ rs : List ρ,
    (∃ r, dispatch m rs = .partial r) ↔ (∀ r ∈ rs, ¬ (m r).IsFull) ∧ ∃ r ∈ rs, m r = .partial
  | [] => by simp [dispatch]
  | r :: rs => by
    have ih := dispatch_partial_iff rs
    have hnone := dispatch_none_iff m rs
    simp only [dispatch, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    cases hm : m r with
    | full b => simp [Match.IsFull]
    | «partial» =>
      simp only [Match.IsFull, not_false_eq_true, true_and, true_or, and_true]
      cases hd : dispatch m rs with
      | found r' b' =>
        simp only [reduceCtorEq, exists_false, false_iff]
        obtain ⟨r'', hr'', hf⟩ := dispatch_found_full m hd
        intro hall; exact hall r'' hr'' hf
      | «partial» r' =>
        simp only [Outcome.partial.injEq, exists_eq', true_iff]
        rw [hd] at ih
        exact (ih.1 ⟨r', rfl⟩).1
      | none =>
        simp only [Outcome.partial.injEq, exists_eq', true_iff]
        intro r'' hr''
        rw [(hnone.1 hd) r'' hr'']; simp
    | none =>
      simp only [Match.IsFull, not_false_eq_true, true_and, reduceCtorEq, false_or]
      exact ih

end Dispatch

/-! ## The HTTP router -/

namespace Route

variable {α : Type}

theorem matches_full_iff (r : Route α) (method path : String) (v : Args r.path.pieces) :
    r.matches method path = .full v ↔ r.path.match path = some v ∧ r.allows method = true := by
  simp only [Route.matches]
  cases h : r.path.match path with
  | none => simp
  | some v' => by_cases ha : r.allows method <;> simp [ha]

theorem matches_partial_iff (r : Route α) (method path : String) :
    r.matches method path = .partial ↔ (r.path.match path).isSome ∧ r.allows method = false := by
  simp only [Route.matches]
  cases h : r.path.match path with
  | none => simp
  | some v' => by_cases ha : r.allows method <;> simp [ha]

theorem matches_none_iff (r : Route α) (method path : String) :
    r.matches method path = .none ↔ r.path.match path = none := by
  simp only [Route.matches]
  cases h : r.path.match path with
  | none => simp
  | some v' => by_cases ha : r.allows method <;> simp [ha]

end Route

namespace Router

variable {α : Type}

/-- **First match.** The router runs `r` with `v` exactly when `r` matches the
method and the path with `v`, and no earlier route matches both. -/
theorem resolve_found_iff (rs : List (Route α)) (method path : String) (r : Route α)
    (v : Args r.path.pieces) :
    resolve rs method path = .found r v ↔
      ∃ pre post, rs = pre ++ r :: post ∧ r.matches method path = .full v ∧
        ∀ r' ∈ pre, ¬ (r'.matches method path).IsFull := by
  rw [← dispatch_found_iff (fun (r : Route α) => r.matches method path)]
  simp only [resolve]
  cases dispatch (fun (r : Route α) => r.matches method path) rs <;> simp

/-- **405 iff partial.** The router answers `405 Method Not Allowed` exactly
when no route matches both the method and the path, and some route matches
the path. -/
theorem methodNotAllowed_iff (rs : List (Route α)) (method path : String) :
    (∃ r allow, resolve rs method path = .methodNotAllowed r allow) ↔
      (∀ r ∈ rs, ¬ (r.matches method path).IsFull) ∧ ∃ r ∈ rs, r.matches method path = .partial := by
  rw [← dispatch_partial_iff (fun (r : Route α) => r.matches method path)]
  simp only [resolve]
  cases dispatch (fun (r : Route α) => r.matches method path) rs <;> simp

/-- The `Allow` list of a `405` is the methods of the first route that
matched the path (as starlette's `Router` does). -/
theorem methodNotAllowed_allow (rs : List (Route α)) (method path : String) (r : Route α)
    (allow : List String) (h : resolve rs method path = .methodNotAllowed r allow) :
    allow = r.methods.getD [] := by
  simp only [resolve] at h
  split at h <;> cases h; rfl

/-- **404 iff no route matches the path.** -/
theorem notFound_iff (rs : List (Route α)) (method path : String) :
    resolve rs method path = .notFound ↔ ∀ r ∈ rs, r.path.match path = none := by
  have := dispatch_none_iff (fun (r : Route α) => r.matches method path) rs
  simp only [Route.matches_none_iff] at this
  rw [← this]
  simp only [resolve]
  cases dispatch (fun (r : Route α) => r.matches method path) rs <;> simp

end Router

end Keel
