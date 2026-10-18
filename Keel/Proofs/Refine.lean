import Keel.RepoImpl.Refine

/-!
# Proofs: the laws of `Keel.Refine`

* `validate_iff`: validation is sound and complete for `holds`.
* `validate_and_iff`: a conjunction validates exactly when both sides do.
* `validate_error_ne_nil`: a failure always says why.
* The validator laws: `at` puts every error under its key, paths compose
  (`atPath_append`), so every error of `v.atPath p` is located under `p`
  (`loc_atPath`); `both` and `each` succeed exactly when every part does, and
  report the errors of every failing part.
-/

namespace Keel

namespace Constraint

variable {α : Type}

/-- Validation returns its input when it succeeds. -/
theorem validate_ok_eq (c : Constraint α) {x y : α} (h : c.validate x = .ok y) : y = x := by
  induction c generalizing y
  case and c d _ ihd =>
    simp only [validate] at h
    split at h
    · exact ihd h
    · cases h
  case or c d _ _ =>
    simp only [validate] at h
    split at h <;> first | (cases h; rfl) | cases h
  all_goals
    simp only [validate] at h
    split at h
    · cases h; rfl
    · cases h

/-- **Validation is sound and complete.** -/
theorem validate_iff (c : Constraint α) (x : α) : c.validate x = .ok x ↔ c.holds x := by
  induction c
  case and c d ihc ihd =>
    simp only [validate, holds]
    cases hc : c.validate x with
    | ok y =>
      have := validate_ok_eq c hc; subst this
      exact ⟨fun h => ⟨ihc.1 hc, ihd.1 h⟩, fun h => ihd.2 h.2⟩
    | error es =>
      simp only [reduceCtorEq, false_iff]
      intro h; rw [ihc.2 h.1] at hc; cases hc
  case or c d ihc ihd =>
    simp only [validate, holds]
    cases hc : c.validate x with
    | ok y =>
      have := validate_ok_eq c hc; subst this
      simp only [true_iff]; exact Or.inl (ihc.1 hc)
    | error e₁ =>
      cases hd : d.validate x with
      | ok y =>
        have := validate_ok_eq d hd; subst this
        simp only [true_iff]; exact Or.inr (ihd.1 hd)
      | error e₂ =>
        simp only [reduceCtorEq, false_iff]
        rintro (h | h)
        · rw [ihc.2 h] at hc; cases hc
        · rw [ihd.2 h] at hd; cases hd
  all_goals
    simp only [validate]
    split <;> simp_all

theorem validate_eq_ok_iff (c : Constraint α) (x y : α) : c.validate x = .ok y ↔ y = x ∧ c.holds x := by
  constructor
  · intro h
    have := validate_ok_eq c h; subst this
    exact ⟨rfl, (validate_iff c y).1 h⟩
  · rintro ⟨rfl, h⟩; exact (validate_iff c y).2 h

/-- A failure always reports at least one error. -/
theorem validate_error_ne_nil (c : Constraint α) {x : α} {es : List (Refine.Error α)}
    (h : c.validate x = .error es) : es ≠ [] := by
  induction c generalizing es
  case and c d ihc ihd =>
    simp only [validate] at h
    split at h
    · exact ihd h
    · cases h; exact ihc (by assumption)
  case or c d ihc _ =>
    simp only [validate] at h
    split at h
    · cases h
    · cases h
    · cases h
      rename_i e₁ e₂ h1 _
      simp only [ne_eq, List.append_eq_nil_iff, not_and]
      intro h'; exact absurd h' (ihc h1)
  all_goals
    simp only [validate] at h
    split at h
    · cases h
    · cases h; simp

/-- Validation fails exactly when the constraint does not hold. -/
theorem validate_error_iff (c : Constraint α) (x : α) :
    (∃ es, c.validate x = .error es) ↔ ¬ c.holds x := by
  rw [← validate_iff]
  cases h : c.validate x with
  | ok y =>
    have := validate_ok_eq c h; subst this; simp
  | error es => simp

/-- **Conjunction validates both.** -/
theorem validate_and_iff (c d : Constraint α) (x : α) :
    (c.and d).validate x = .ok x ↔ c.validate x = .ok x ∧ d.validate x = .ok x := by
  rw [validate_iff, validate_iff, validate_iff]; rfl

/-- A failing conjunction reports the first failing side. -/
theorem validate_and_error (c d : Constraint α) (x : α) (es : List (Refine.Error α))
    (h : c.validate x = .error es) : (c.and d).validate x = .error es := by
  simp [validate, h]

/-- Disjunction validates either. -/
theorem validate_or_iff (c d : Constraint α) (x : α) :
    (c.or d).validate x = .ok x ↔ c.validate x = .ok x ∨ d.validate x = .ok x := by
  rw [validate_iff, validate_iff, validate_iff]; rfl

/-- Errors from a constraint are located at the value itself. -/
theorem loc_validate (c : Constraint α) {x : α} {es : List (Refine.Error α)}
    (h : c.validate x = .error es) : ∀ e ∈ es, e.loc = [] := by
  induction c generalizing es
  case and c d ihc ihd =>
    simp only [validate] at h
    split at h
    · exact ihd h
    · cases h; exact ihc (by assumption)
  case or c d ihc ihd =>
    simp only [validate] at h
    split at h
    · cases h
    · cases h
    · cases h
      rename_i e₁ e₂ h1 h2
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact ihc h1 e he
      · exact ihd h2 e he
  all_goals
    simp only [validate] at h
    split at h
    · cases h
    · cases h; simp

end Constraint

namespace Validator

variable {ε ι α β : Type}

@[simp] theorem at_apply [Located ε] (k : PathElem) (v : Validator ε ι α) (x : ι) :
    (v.at k) x = (v x).mapError (List.map (Located.within k)) := rfl

theorem at_ok_iff [Located ε] (k : PathElem) (v : Validator ε ι α) (x : ι) (a : α) :
    (v.at k) x = .ok a ↔ v x = .ok a := by
  simp only [at_apply]
  cases v x <;> simp [Except.mapError]

/-- **Errors move under their key.** Every error of `v.at k` is an error of `v`
placed under `k`. -/
theorem at_error_iff [Located ε] (k : PathElem) (v : Validator ε ι α) (x : ι) (es : List ε) :
    (v.at k) x = .error es ↔ ∃ es', v x = .error es' ∧ es = es'.map (Located.within k) := by
  simp only [at_apply]
  cases v x <;> simp [Except.mapError, eq_comm]

@[simp] theorem atPath_nil [Located ε] (v : Validator ε ι α) : v.atPath [] = v := rfl

@[simp] theorem atPath_cons [Located ε] (k : PathElem) (p : Loc) (v : Validator ε ι α) :
    v.atPath (k :: p) = (v.atPath p).at k := rfl

/-- **Paths compose.** -/
theorem atPath_append [Located ε] (p q : Loc) (v : Validator ε ι α) :
    v.atPath (p ++ q) = (v.atPath q).atPath p := by
  simp [atPath, List.foldr_append]

/-- **Error locations prefix-compose.** Every error of `v.atPath p` is located
under `p`, followed by where `v` located it. -/
theorem loc_atPath [Located ε] : ∀ (p : Loc) (v : Validator ε ι α) (x : ι) (es : List ε),
    (v.atPath p) x = .error es → ∀ e ∈ es, ∃ e' : ε, Located.loc e = p ++ Located.loc e'
  | [], _, _, _, _ => fun e _ => ⟨e, rfl⟩
  | k :: p, v, x, es, h => by
    rw [atPath_cons, at_error_iff] at h
    obtain ⟨es', h', rfl⟩ := h
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    obtain ⟨e', hl⟩ := loc_atPath p v x es' h' e₀ he₀
    exact ⟨e', by rw [Located.loc_within, hl]; rfl⟩

/-- `p` is a prefix of the location of every error of `v.atPath p`. -/
theorem prefix_loc_atPath [Located ε] (p : Loc) (v : Validator ε ι α) (x : ι) (es : List ε)
    (h : (v.atPath p) x = .error es) : ∀ e ∈ es, p <+: Located.loc e := by
  intro e he
  obtain ⟨e', hl⟩ := loc_atPath p v x es h e he
  exact ⟨_, hl.symm⟩

theorem both_ok_iff (v : Validator ε ι α) (w : Validator ε ι β) (x : ι) (a : α) (b : β) :
    (v.both w) x = .ok (a, b) ↔ v x = .ok a ∧ w x = .ok b := by
  simp only [both]
  cases v x <;> cases w x <;> simp

/-- A failing `both` reports exactly the errors of the failing sides. -/
theorem both_error (v : Validator ε ι α) (w : Validator ε ι β) (x : ι) (es : List ε)
    (h : (v.both w) x = .error es) :
    es = (match v x with | .error e => e | .ok _ => []) ++
      (match w x with | .error e => e | .ok _ => []) := by
  simp only [both] at h
  cases hv : v x <;> cases hw : w x <;> simp only [hv, hw, reduceCtorEq, Except.error.injEq] at h ⊢ <;>
    simp [h]

theorem eachFrom_ok_iff [Located ε] (v : Validator ε ι α) :
    ∀ (i : Nat) (xs : List ι) (ys : List α), eachFrom v i xs = .ok ys ↔ xs.mapM v = .ok ys
  | _, [], ys => by simp [eachFrom, eq_comm, pure, Except.pure]
  | i, x :: xs, ys => by
    have ih := eachFrom_ok_iff v (i + 1) xs
    simp only [eachFrom, List.mapM_cons]
    have hat := at_ok_iff (.index i) v x
    cases hv : v x with
    | ok a =>
      have : (v.at (.index i)) x = .ok a := (hat a).2 hv
      rw [this]
      cases he : eachFrom v (i + 1) xs with
      | ok as =>
        have hm := (ih as).1 he
        simp [hm, bind, Except.bind, eq_comm, pure, Except.pure]
      | error e =>
        cases hm : xs.mapM v with
        | ok as => exact absurd ((ih as).2 hm) (by rw [he]; simp)
        | error e' => simp [bind, Except.bind]
    | error e =>
      have : (v.at (.index i)) x = .error (e.map (Located.within (.index i))) := by
        simp [hv, Except.mapError]
      rw [this]
      cases eachFrom v (i + 1) xs <;> simp [bind, Except.bind]

/-- **`each` succeeds exactly when every element does**, with the same values
as validating them in turn. -/
theorem each_ok_iff [Located ε] (v : Validator ε ι α) (xs : List ι) (ys : List α) :
    (each v) xs = .ok ys ↔ xs.mapM v = .ok ys := eachFrom_ok_iff v 0 xs ys

theorem loc_eachFrom [Located ε] (v : Validator ε ι α) :
    ∀ (i : Nat) (xs : List ι) (es : List ε), eachFrom v i xs = .error es →
      ∀ e ∈ es, ∃ j, i ≤ j ∧ j < i + xs.length ∧ ∃ e' : ε, Located.loc e = .index j :: Located.loc e'
  | _, [], es, h => by simp [eachFrom] at h
  | i, x :: xs, es, h => by
    have ih := loc_eachFrom v (i + 1) xs
    have hat : ∀ es', (v.at (.index i)) x = .error es' → ∀ e ∈ es',
        ∃ e' : ε, Located.loc e = .index i :: Located.loc e' := by
      intro es' h' e he
      obtain ⟨e', hl⟩ := loc_atPath [.index i] v x es' h' e he
      exact ⟨e', hl⟩
    simp only [eachFrom] at h
    intro e he
    split at h
    · cases h
    · cases h
      obtain ⟨e', hl⟩ := hat _ (by assumption) e he
      exact ⟨i, Nat.le_refl _, by simp, e', hl⟩
    · cases h
      obtain ⟨j, hj1, hj2, rest⟩ := ih _ (by assumption) e he
      exact ⟨j, by omega, by simp; omega, rest⟩
    · cases h; rename_i h1 h2
      rcases List.mem_append.1 he with he | he
      · obtain ⟨e', hl⟩ := hat _ h1 e he
        exact ⟨i, Nat.le_refl _, by simp, e', hl⟩
      · obtain ⟨j, hj1, hj2, rest⟩ := ih _ h2 e he
        exact ⟨j, by omega, by simp; omega, rest⟩

/-- Every error of `each v` is located under the index of an element. -/
theorem loc_each [Located ε] (v : Validator ε ι α) (xs : List ι) (es : List ε)
    (h : (each v) xs = .error es) :
    ∀ e ∈ es, ∃ j < xs.length, ∃ e' : ε, Located.loc e = .index j :: Located.loc e' := by
  intro e he
  obtain ⟨j, _, hj, rest⟩ := loc_eachFrom v 0 xs es h e he
  exact ⟨j, by omega, rest⟩

end Validator

end Keel
