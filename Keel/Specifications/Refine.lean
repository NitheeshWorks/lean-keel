import Keel.APIs.Refine

/-!
# Specifications: refinement and validation

The headline laws of `Keel.Refine`, proved in `Proofs/Refine.lean` and
`APIs/Refine.lean`, with slots in `Proofs/Verified.lean`.
-/

namespace Keel.Spec

open Constraint Validator

/-- Validation is sound and complete: it succeeds, returning its input,
exactly when the constraint holds. -/
def ValidateIff : Prop :=
  ∀ (α : Type) (c : Constraint α) (x : α), c.validate x = .ok x ↔ c.holds x

/-- A failed validation always reports an error. -/
def ValidateErrorsNonempty : Prop :=
  ∀ (α : Type) (c : Constraint α) (x : α) (es : List (Refine.Error α)),
    c.validate x = .error es → es ≠ []

/-- A conjunction validates exactly when both sides do. -/
def ValidateAnd : Prop :=
  ∀ (α : Type) (c d : Constraint α) (x : α),
    (c.and d).validate x = .ok x ↔ c.validate x = .ok x ∧ d.validate x = .ok x

/-- Refining succeeds exactly when the constraint holds. -/
def RefineIff : Prop :=
  ∀ (α : Type) (c : Constraint α) (x : α), (∃ y, c.refine x = .ok y) ↔ c.holds x

/-- Locations compose along paths. -/
def AtPathAppend : Prop :=
  ∀ (ε ι α : Type) [Located ε] (p q : Loc) (v : Validator ε ι α),
    v.atPath (p ++ q) = (v.atPath q).atPath p

/-- Every error of a validator placed under a path is located under it. -/
def LocAtPath : Prop :=
  ∀ (ε ι α : Type) [Located ε] (p : Loc) (v : Validator ε ι α) (x : ι) (es : List ε),
    (v.atPath p) x = .error es → ∀ e ∈ es, p <+: Located.loc e

/-- `both` succeeds exactly when both validators do. -/
def BothOkIff : Prop :=
  ∀ (ε ι α β : Type) (v : Validator ε ι α) (w : Validator ε ι β) (x : ι) (a : α) (b : β),
    (v.both w) x = .ok (a, b) ↔ v x = .ok a ∧ w x = .ok b

/-- `each` succeeds exactly when every element does. -/
def EachOkIff : Prop :=
  ∀ (ε ι α : Type) [Located ε] (v : Validator ε ι α) (xs : List ι) (ys : List α),
    (each v) xs = .ok ys ↔ xs.mapM v = .ok ys

/-- Every error of `each` is located under an element's index. -/
def LocEach : Prop :=
  ∀ (ε ι α : Type) [Located ε] (v : Validator ε ι α) (xs : List ι) (es : List ε),
    (each v) xs = .error es →
      ∀ e ∈ es, ∃ j < xs.length, ∃ e' : ε, Located.loc e = .index j :: Located.loc e'

end Keel.Spec
