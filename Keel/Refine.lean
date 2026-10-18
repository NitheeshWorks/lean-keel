import Keel.APIs.Refine

/-!
# Keel.Refine: refinement and validation

A constraint language (`gt ge lt le multipleOf minLength maxLength pattern
oneOf`, `and or not`), its meaning `Constraint.holds` with a decision
procedure, the refinement type `α ∣ c` (with `open Keel`), validation that is
sound and complete (`Constraint.validate_iff`), and validators whose errors
carry locations that compose along paths (`Validator.loc_atPath`).
-/
