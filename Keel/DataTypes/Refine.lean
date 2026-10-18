/-!
# Refinement: the constraint language and located errors

`Constraint α` is a small language of predicates on `α`: the bounds `gt ge lt
le`, `multipleOf`, the lengths `minLength maxLength`, `pattern`, `oneOf`, and
`and or not`. One definition gives the predicate (`Constraint.holds`), its
decision procedure, the validator and its errors, so they cannot disagree.
Downstream, the same constraint also gives the JSON Schema keywords
(lean-pydantic) and the option-type checks (lean-click).

Each atom applies to the types that support it, through a small class:
`Ordered` for bounds, `Divisible` for `multipleOf`, `Sized` for lengths,
`Textual` for `pattern`. The class instance is stored in the constructor, so a
`Constraint String` cannot hold a numeric bound unless `String` is `Ordered`.

Errors carry a location, a path of keys and indices (`Loc`), as pydantic's
`loc` does. The class `Located` lets any error type take part in the
location theorems.
-/

namespace Keel

/-- Types with decidable `<` and `≤`, for the bound constraints. -/
class Ordered (α : Type) extends LT α, LE α where
  decLT : ∀ a b : α, Decidable (a < b)
  decLE : ∀ a b : α, Decidable (a ≤ b)

instance : Ordered Nat := { decLT := inferInstance, decLE := inferInstance }
instance : Ordered Int := { decLT := inferInstance, decLE := inferInstance }

/-- Types with a decidable "is a multiple of". -/
class Divisible (α : Type) where
  /-- `IsMultiple k x`: `x` is a multiple of `k`. -/
  IsMultiple : α → α → Prop
  dec : ∀ k x, Decidable (IsMultiple k x)

instance : Divisible Nat := ⟨fun k x => k ∣ x, fun _ _ => inferInstance⟩
instance : Divisible Int := ⟨fun k x => k ∣ x, fun _ _ => inferInstance⟩

/-- Types with a length, for `minLength` and `maxLength`. A string's length is
its number of characters, as in Python. -/
class Sized (α : Type) where
  size : α → Nat

instance : Sized String := ⟨String.length⟩
instance {β : Type} : Sized (List β) := ⟨List.length⟩
instance {β : Type} : Sized (Array β) := ⟨Array.size⟩
instance : Sized ByteArray := ⟨ByteArray.size⟩

/-- Types a `pattern` can test. -/
class Textual (α : Type) where
  text : α → String

instance : Textual String := ⟨id⟩

/-- A pattern: its source (for schemas and messages) and its matcher. Keel
does not fix a regular-expression language; lean-pydantic supplies a
verified matcher and its source together. -/
structure Pattern where
  source : String
  test : String → Bool

/-- The constraint language. -/
inductive Constraint (α : Type) where
  | gt [Ordered α] (bound : α)
  | ge [Ordered α] (bound : α)
  | lt [Ordered α] (bound : α)
  | le [Ordered α] (bound : α)
  | multipleOf [Divisible α] (k : α)
  | minLength [Sized α] (n : Nat)
  | maxLength [Sized α] (n : Nat)
  | pattern [Textual α] (p : Pattern)
  | oneOf [DecidableEq α] (choices : List α)
  /-- Membership up to a normalisation (click's case-insensitive `Choice`). -/
  | oneOfBy [DecidableEq α] (norm : α → α) (choices : List α)
  | and (c d : Constraint α)
  | or (c d : Constraint α)
  | not (c : Constraint α)

/-- One step of a location: a field name or a list index. -/
inductive PathElem where
  | key (name : String)
  | index (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A location: the path from the validated value to the failing part,
outermost first. -/
abbrev Loc := List PathElem

/-- Error types that carry a location, which can be extended at the front. -/
class Located (ε : Type) where
  loc : ε → Loc
  /-- The same error, one step further out. -/
  within : PathElem → ε → ε
  loc_within : ∀ k e, loc (within k e) = k :: loc e

/-- A failed constraint: where, which atom (or `not`/`or` node) failed, and
the value it failed on. -/
structure Refine.Error (α : Type) where
  loc : Loc
  failed : Constraint α
  input : α

instance {α : Type} : Located (Refine.Error α) where
  loc e := e.loc
  within k e := { e with loc := k :: e.loc }
  loc_within _ _ := rfl

end Keel
