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
  | oneOfBy norm cs, x => ∃ c ∈ cs, norm c = norm x
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
  | @oneOfBy _ _ norm cs, x => decidable_of_iff (cs.any fun c => decide (norm c = norm x) = true) (by simp [holds])
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

/-- The constraint language, as syntax: the atoms (`gt 0`, `maxLength 50`,
`oneOf ["a", "b"]`, …), `∧`, `∨`, `¬` and parentheses. Atom names are
non-reserved keywords, so they stay usable as identifiers elsewhere. -/
declare_syntax_cat refinement (behavior := both)
syntax:30 refinement:31 " ∨ " refinement:30 : refinement
syntax:35 refinement:36 " ∧ " refinement:35 : refinement
syntax:max "¬" refinement:max : refinement
syntax:max "(" refinement ")" : refinement
syntax:max (name := refineGt) &"gt" term:max : refinement
syntax:max (name := refineGe) &"ge" term:max : refinement
syntax:max (name := refineLt) &"lt" term:max : refinement
syntax:max (name := refineLe) &"le" term:max : refinement
syntax:max (name := refineMultipleOf) &"multipleOf" term:max : refinement
syntax:max (name := refineMinLength) &"minLength" term:max : refinement
syntax:max (name := refineMaxLength) &"maxLength" term:max : refinement
syntax:max (name := refinePattern) &"pattern" term:max : refinement
syntax:max (name := refineOneOf) &"oneOf" term:max : refinement
syntax:max (name := refineOneOfBy) &"oneOfBy" term:max term:max : refinement

open Lean in
/-- Each atom's syntax and the constructor it stands for. -/
def refinementAtoms : List (Name × Name) :=
  [(``refineGt, ``Constraint.gt), (``refineGe, ``Constraint.ge), (``refineLt, ``Constraint.lt),
   (``refineLe, ``Constraint.le), (``refineMultipleOf, ``Constraint.multipleOf),
   (``refineMinLength, ``Constraint.minLength), (``refineMaxLength, ``Constraint.maxLength),
   (``refinePattern, ``Constraint.pattern), (``refineOneOf, ``Constraint.oneOf),
   (``refineOneOfBy, ``Constraint.oneOfBy)]

/-- Internal: a `refinement` as a `Constraint` term. -/
syntax "refinement% " refinement : term

open Lean in
macro_rules
  | `(refinement% $a ∨ $b) => `(Constraint.or (refinement% $a) (refinement% $b))
  | `(refinement% $a ∧ $b) => `(Constraint.and (refinement% $a) (refinement% $b))
  | `(refinement% ¬ $a) => `(Constraint.not (refinement% $a))
  | `(refinement% ($a)) => `(refinement% $a)
  | `(refinement% $r) => do
    match refinementAtoms.lookup r.raw.getKind with
    | some f =>
      let args := (r.raw.getArgs.toList.drop 1).map fun a => (⟨a⟩ : TSyntax `term)
      `($(mkIdent f) $(args.toArray)*)
    | none => Macro.throwUnsupported

/-- `α ∣ c`: the values of `α` satisfying the constraint `c`. Takes precedence
over divisibility only when the right side is in the constraint language (it
starts with a constraint name), so `3 ∣ n` and `k ∣ n ∧ k ∣ m` keep their
meaning. A constraint held in a variable is written `Refined α c`. -/
scoped syntax:50 (priority := high) term:51 " ∣ " refinement : term

macro_rules
  | `($a ∣ $r:refinement) => `(Refined $a (refinement% $r))

end Keel
