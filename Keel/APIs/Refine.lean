import Keel.Proofs.Refine

/-!
# APIs: refining values

`Constraint.refine c x` checks `x` and returns it as an element of `α ∣ c`,
carrying its proof, or the errors. `Validator.ofConstraint c` is the same as
a validator, to place under paths and combine with `both` and `each`.
-/

namespace Keel

namespace Constraint

variable {α : Type}

/-- Check `x` against `c`: the refined value, or the errors of
`c.validate x` (never empty). -/
def refine (c : Constraint α) (x : α) : Except (List (Refine.Error α)) (Refined α c) :=
  match h : c.validate x with
  | .ok y => .ok ⟨x, (validate_eq_ok_iff c x y).1 h |>.2⟩
  | .error es => .error es

/-- `refine` succeeds exactly when the constraint holds, with the input. -/
theorem refine_ok_iff (c : Constraint α) (x : α) :
    (∃ y, c.refine x = .ok y) ↔ c.holds x := by
  unfold refine
  constructor
  · rintro ⟨y, hy⟩
    split at hy
    · rename_i y' h; exact ((validate_eq_ok_iff c x y').1 h).2
    · cases hy
  · intro h
    split
    · exact ⟨_, rfl⟩
    · rename_i es he; rw [(validate_iff c x).2 h] at he; cases he

/-- A refined value is the input. -/
theorem refine_val (c : Constraint α) {x : α} {y : Refined α c} (h : c.refine x = .ok y) :
    y.val = x := by
  unfold refine at h
  split at h
  · cases h; rfl
  · cases h

/-- `refine` fails with the errors `validate` reports. -/
theorem refine_error (c : Constraint α) {x : α} {es : List (Refine.Error α)} :
    c.refine x = .error es ↔ c.validate x = .error es := by
  unfold refine
  split <;> rename_i h <;> simp [h]

end Constraint

/-- A constraint as a validator, producing the refined value. -/
def Validator.ofConstraint {α : Type} (c : Constraint α) : Validator (Refine.Error α) α (Refined α c) :=
  c.refine

end Keel
