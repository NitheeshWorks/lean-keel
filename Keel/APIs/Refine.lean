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

/-- **A choice, up to a normalisation** (click's `Choice.convert` with
`case_sensitive=False`): the *first declared* choice equal to `x` after
`norm`, which is what click returns, not `x` itself. -/
def pick [DecidableEq α] (norm : α → α) (cs : List α) (x : α) :
    Except (List (Refine.Error α)) {c // c ∈ cs} :=
  match h : cs.find? (fun c => decide (norm c = norm x)) with
  | some c => .ok ⟨c, List.mem_of_find?_eq_some h⟩
  | none => .error [⟨[], .oneOfBy norm cs, x⟩]

/-- `pick` returns exactly what `find?` finds. -/
theorem pick_ok_iff [DecidableEq α] (norm : α → α) (cs : List α) (x v : α) :
    (∃ c, pick norm cs x = .ok c ∧ c.val = v) ↔ cs.find? (fun c => decide (norm c = norm x)) = some v := by
  unfold pick
  split
  · rename_i c hc
    simp only [Except.ok.injEq]
    constructor
    · rintro ⟨_, rfl, rfl⟩; exact hc
    · intro h; rw [hc] at h; cases h; exact ⟨_, rfl, rfl⟩
  · rename_i hc
    simp [hc]

/-- `pick` succeeds exactly when `oneOfBy` holds. -/
theorem pick_isOk_iff [DecidableEq α] (norm : α → α) (cs : List α) (x : α) :
    (∃ c, pick norm cs x = .ok c) ↔ (oneOfBy norm cs).holds x := by
  unfold pick
  simp only [holds]
  split
  · rename_i c hc
    have := List.find?_some hc
    exact ⟨fun _ => ⟨c, List.mem_of_find?_eq_some hc, by simpa using this⟩, fun _ => ⟨_, rfl⟩⟩
  · rename_i hc
    simp only [reduceCtorEq, exists_false, false_iff, not_exists, not_and]
    intro c hc' he
    have := List.find?_eq_none.1 hc c hc'
    simp [he] at this

end Constraint

/-- A constraint as a validator, producing the refined value. -/
def Validator.ofConstraint {α : Type} (c : Constraint α) : Validator (Refine.Error α) α (Refined α c) :=
  c.refine

/-! ## One error type for a whole model

A model's fields have different types, so their `Refine.Error α` differ. A
`Refine.Issue` erases the type: the location, the kind of the constraint that
failed, and the input as text, which is what a validation report shows. -/

/-- The kind of a constraint, by pydantic's error-type names. -/
def Constraint.kind {α : Type} : Constraint α → String
  | @Constraint.gt _ _ _ => "greater_than"
  | @Constraint.ge _ _ _ => "greater_than_equal"
  | @Constraint.lt _ _ _ => "less_than"
  | @Constraint.le _ _ _ => "less_than_equal"
  | @Constraint.multipleOf _ _ _ => "multiple_of"
  | @Constraint.minLength _ _ _ => "too_short"
  | @Constraint.maxLength _ _ _ => "too_long"
  | @Constraint.pattern _ _ _ => "string_pattern_mismatch"
  | @Constraint.oneOf _ _ _ => "literal_error"
  | @Constraint.oneOfBy _ _ _ _ => "literal_error"
  | .and _ _ => "and"
  | .or _ _ => "or"
  | .not _ => "not"

/-- A located validation issue, of any field type. -/
structure Refine.Issue where
  loc : Loc
  kind : String
  input : String
  deriving DecidableEq, Repr

instance : Located Refine.Issue where
  loc e := e.loc
  within k e := { e with loc := k :: e.loc }
  loc_within _ _ := rfl

/-- Erase the field type of an error. -/
def Refine.Error.toIssue {α : Type} [ToString α] (e : Refine.Error α) : Refine.Issue :=
  ⟨e.loc, e.failed.kind, toString e.input⟩

namespace Validator

variable {ε ι ι' α β : Type}

/-- Check a constraint, reporting `Refine.Issue`s. -/
def check {α : Type} [ToString α] (c : Constraint α) : Validator Refine.Issue α (Refined α c) :=
  fun x => (c.refine x).mapError (List.map Refine.Error.toIssue)

/-- Validate the field read by `get`, with its errors under the key `k`. -/
def field [Located ε] (k : String) (get : ι → ι') (v : Validator ε ι' α) : Validator ε ι α :=
  Validator.at (.key k) (fun x => v (get x))

/-- Transform the value of a success. -/
def map (f : α → β) (v : Validator ε ι α) : Validator ε ι β := fun x => (v x).map f

theorem check_ok_iff {α : Type} [ToString α] (c : Constraint α) (x : α) :
    (∃ y, check c x = .ok y) ↔ c.holds x := by
  rw [← Constraint.refine_ok_iff]
  simp only [check]
  cases c.refine x <;> simp [Except.mapError]

/-- Errors of a constraint check are at the value itself. -/
theorem loc_check {α : Type} [ToString α] (c : Constraint α) (x : α) (es : List Refine.Issue)
    (h : check c x = .error es) : ∀ e ∈ es, e.loc = [] := by
  simp only [check] at h
  cases hr : c.refine x with
  | ok y => rw [hr] at h; cases h
  | error es' =>
    rw [hr] at h
    simp only [Except.mapError, Except.error.injEq] at h
    subst h
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact Constraint.loc_validate c (Constraint.refine_error c |>.1 hr) e' he'

theorem field_apply [Located ε] (k : String) (get : ι → ι') (v : Validator ε ι' α) (x : ι) :
    field k get v x = (v (get x)).mapError (List.map (Located.within (.key k))) := rfl

theorem map_ok_iff (f : α → β) (v : Validator ε ι α) (x : ι) (b : β) :
    map f v x = .ok b ↔ ∃ a, v x = .ok a ∧ f a = b := by
  simp only [map]
  cases v x <;> simp [Except.map]

theorem map_error_iff (f : α → β) (v : Validator ε ι α) (x : ι) (es : List ε) :
    map f v x = .error es ↔ v x = .error es := by
  simp only [map]
  cases v x <;> simp [Except.map]

end Validator

end Keel
