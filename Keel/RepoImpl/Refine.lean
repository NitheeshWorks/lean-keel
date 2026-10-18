import Keel.DataTypes.Refine

/-!
# Refinement: meaning, validation, validators, notation

* `Constraint.holds c x`: what `c` says about `x`, with a `Decidable` instance.
* `Constraint.validate c x`: `x` back, or the errors. `and` checks left to
  right and stops at the first failure (pydantic reports the first violated
  constraint of a field); `or` reports both sides' errors when both fail.
* `Validator ε ι α`: a function from raw input to a value or a list of
  located errors, with combinators that move errors under a path element
  (`at`), run two validators and keep both sides' errors (`both`), and
  validate every element of a list under its index (`each`).
* `α ∣ c`: with `open Keel`, the type of `α` values satisfying `c`, written
  in the constraint language: `String ∣ maxLength 50 ∧ minLength 3`.
-/

namespace Keel

namespace Constraint

variable {α : Type}

/-- What a constraint says about a value. -/
def holds : Constraint α → α → Prop
  | gt b, x => b < x
  | ge b, x => b ≤ x
  | lt b, x => x < b
  | le b, x => x ≤ b
  | multipleOf k, x => Divisible.IsMultiple k x
  | minLength n, x => n ≤ Sized.size x
  | maxLength n, x => Sized.size x ≤ n
  | pattern p, x => p.test (Textual.text x) = true
  | oneOf cs, x => x ∈ cs
  | and c d, x => c.holds x ∧ d.holds x
  | or c d, x => c.holds x ∨ d.holds x
  | not c, x => ¬ c.holds x

/-- Every constraint is decidable. -/
instance decHolds : (c : Constraint α) → (x : α) → Decidable (c.holds x)
  | @gt _ i b, x => i.decLT b x
  | @ge _ i b, x => i.decLE b x
  | @lt _ i b, x => i.decLT x b
  | @le _ i b, x => i.decLE x b
  | @multipleOf _ i k, x => i.dec k x
  | minLength _, _ => Nat.decLe _ _
  | maxLength _, _ => Nat.decLe _ _
  | pattern _, _ => instDecidableEqBool _ _
  | @oneOf _ _ cs, x => List.instDecidableMemOfLawfulBEq x cs
  | and c d, x =>
    match decHolds c x, decHolds d x with
    | isTrue h1, isTrue h2 => isTrue ⟨h1, h2⟩
    | isFalse h1, _ => isFalse fun h => h1 h.1
    | _, isFalse h2 => isFalse fun h => h2 h.2
  | or c d, x =>
    match decHolds c x, decHolds d x with
    | isTrue h1, _ => isTrue (Or.inl h1)
    | _, isTrue h2 => isTrue (Or.inr h2)
    | isFalse h1, isFalse h2 => isFalse fun h => h.elim h1 h2
  | not c, x =>
    match decHolds c x with
    | isTrue h => isFalse fun h' => h' h
    | isFalse h => isTrue h

/-- Check a value: itself, or the errors. Errors are located at `[]`; a
validator places them (`Validator.at`). -/
def validate : Constraint α → α → Except (List (Refine.Error α)) α
  | and c d, x =>
    match validate c x with
    | .ok _ => validate d x
    | .error es => .error es
  | or c d, x =>
    match validate c x, validate d x with
    | .ok _, _ => .ok x
    | _, .ok _ => .ok x
    | .error e₁, .error e₂ => .error (e₁ ++ e₂)
  | c, x => if c.holds x then .ok x else .error [⟨[], c, x⟩]

end Constraint

/-- The values of `α` that satisfy `c`. Written `α ∣ c` with `open Keel`. -/
abbrev Refined (α : Type) (c : Constraint α) : Type := {x : α // c.holds x}

/-! ## Validators -/

/-- A validator from raw input `ι` to `α`: a value, or a list of errors. -/
abbrev Validator (ε ι α : Type) : Type := ι → Except (List ε) α

namespace Validator

variable {ε ι α β : Type}

/-- The errors of `v`, one step further in: under the key or index `k`. -/
def «at» [Located ε] (k : PathElem) (v : Validator ε ι α) : Validator ε ι α :=
  fun x => (v x).mapError (List.map (Located.within k))

/-- Under a whole path, outermost first. -/
def atPath [Located ε] (p : Loc) (v : Validator ε ι α) : Validator ε ι α :=
  p.foldr Validator.at v

/-- Run both; succeed when both do, and otherwise report every error of
both (as a model reports every failing field). -/
def both (v : Validator ε ι α) (w : Validator ε ι β) : Validator ε ι (α × β) := fun x =>
  match v x, w x with
  | .ok a, .ok b => .ok (a, b)
  | .error e, .ok _ => .error e
  | .ok _, .error e => .error e
  | .error e₁, .error e₂ => .error (e₁ ++ e₂)

/-- The list loop of `each`, from index `i`. -/
def eachFrom [Located ε] (v : Validator ε ι α) : Nat → List ι → Except (List ε) (List α)
  | _, [] => .ok []
  | i, x :: xs =>
    match (v.at (.index i)) x, eachFrom v (i + 1) xs with
    | .ok a, .ok as => .ok (a :: as)
    | .error e, .ok _ => .error e
    | .ok _, .error e => .error e
    | .error e₁, .error e₂ => .error (e₁ ++ e₂)

/-- Validate every element, each under its index; report every element's
errors. -/
def each [Located ε] (v : Validator ε ι α) : Validator ε (List ι) (List α) := eachFrom v 0

/-- `v`, then `w` on its value (stops at the first failure). -/
def andThen (v : Validator ε ι α) (w : Validator ε α β) : Validator ε ι β := fun x =>
  match v x with
  | .ok a => w a
  | .error e => .error e

end Validator

/-! ## Notation: `α ∣ c` -/

/-- The constraint language, as syntax: atoms (`gt 0`, `maxLength 50`, a
constraint-valued term), `∧`, `∨`, `¬`, parentheses. -/
declare_syntax_cat refinement
syntax:30 refinement:31 " ∨ " refinement:30 : refinement
syntax:35 refinement:36 " ∧ " refinement:35 : refinement
syntax:max "¬" refinement:max : refinement
syntax:max "(" refinement ")" : refinement
syntax:max ident (ppSpace colGt term:max)* : refinement

/-- The atoms of the constraint language, as written inside `α ∣ …`. -/
def atomNames : List Lean.Name :=
  [`gt, `ge, `lt, `le, `multipleOf, `minLength, `maxLength, `pattern, `oneOf]

/-- Internal: a `refinement` as a `Constraint` term. -/
syntax "refinement% " refinement : term

macro_rules
  | `(refinement% $a ∨ $b) => `(Constraint.or (refinement% $a) (refinement% $b))
  | `(refinement% $a ∧ $b) => `(Constraint.and (refinement% $a) (refinement% $b))
  | `(refinement% ¬ $a) => `(Constraint.not (refinement% $a))
  | `(refinement% ($a)) => `(refinement% $a)
  | `(refinement% $f:ident $args:term*) =>
    if atomNames.contains f.getId then
      `($(Lean.mkIdent (`Keel.Constraint ++ f.getId)) $args*)
    else `($f $args*)

/-- `α ∣ c`: the values of `α` satisfying the constraint `c`. -/
scoped syntax:50 term:51 " ∣ " refinement : term

macro_rules
  | `($a ∣ $r:refinement) => `(Refined $a (refinement% $r))

end Keel
