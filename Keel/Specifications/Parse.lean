import Keel.RepoImpl.Parse

/-!
# Specifications: total parsing

The headline laws of `Keel.Parse`, stated in `Prop`. Each is proved in
`Proofs/Parse.lean` and has a slot in `Proofs/Verified.lean`.

Totality is not a property here: it is the type. Every `Parser` is a total
function, `many` and `fix` are defined by well-founded recursion on the
tokens left, and the library has no `partial` and no fuel. What the laws
state is the meaning: each combinator as an equation on lists.
-/

namespace Keel.Spec

open Parser

/-- A parser is determined by what it does to lists. -/
def ParseExt : Prop :=
  ∀ (τ ε α : Type) (p q : Parser τ ε α), (∀ l, p.parse l = q.parse l) → p = q

/-- On any buffer, a parser does what its list meaning says, at the
corresponding position. -/
def RunOfParse : Prop :=
  ∀ (τ ε α σ : Type) [Input σ τ] (p : Parser τ ε α) (s : σ) (i : Nat) (a : α) (r : List τ),
    p.parse (Input.rest s i) = .ok a r → i ≤ Input.size s →
      p.run s i = .ok a (Input.size s - r.length)

/-- Sequencing continues on what the first parser left. -/
def ParseBind : Prop :=
  ∀ (τ ε α β : Type) (p : Parser τ ε α) (f : α → Parser τ ε β) (l : List τ),
    (p >>= f).parse l = (p.parse l).bind fun a r => (f a).parse r

/-- Choice is committed: the second alternative runs only when the first
failed without consuming. -/
def ParseOrElse : Prop :=
  ∀ (τ ε α : Type) (p q : Parser τ ε α) (l : List τ),
    (p <|> q).parse l =
      match p.parse l with
      | .ok a r => .ok a r
      | .error e r => if r.length = l.length then q.parse l else .error e r

/-- A literal reads itself on any continuation. -/
def ParseLit : Prop :=
  ∀ (τ ε : Type) [ParseError ε] [DecidableEq τ] (l r : List τ),
    (lit l : Parser τ ε Unit).parse (l ++ r) = .ok () r

/-- `startsWith` decides the prefix relation without consuming. -/
def ParseStartsWith : Prop :=
  ∀ (τ ε : Type) [ParseError ε] [DecidableEq τ] (l x : List τ),
    (startsWith l : Parser τ ε Bool).parse x = .ok (decide (l <+: x)) x

/-- `many` unfolds once, continuing only after a step that consumed. -/
def ParseMany : Prop :=
  ∀ (τ ε α : Type) (p : Parser τ ε α) (l : List τ),
    (many p).parse l =
      match p.parse l with
      | .ok a r => if r.length = l.length then .ok [] l else ((many p).parse r).map (a :: ·)
      | .error e r => if r.length = l.length then .ok [] l else .error e r

/-- `takeWhile f` is `List.takeWhile f`, with `List.dropWhile f` left. -/
def ParseTakeWhile : Prop :=
  ∀ (τ ε : Type) [ParseError ε] (f : τ → Bool) (l : List τ),
    (takeWhile f : Parser τ ε (List τ)).parse l = .ok (l.takeWhile f) (l.dropWhile f)

/-- The fixpoint unfolds to `F` applied to the handle for the current length. -/
def ParseFix : Prop :=
  ∀ (τ ε α : Type) [ParseError ε] (F : Parser τ ε α → Parser τ ε α) (l : List τ),
    (fix F).parse l = (F (below F l.length)).parse l

/-- The handle is the fixpoint on fewer tokens, and `stuck` otherwise. -/
def ParseBelow : Prop :=
  ∀ (τ ε α : Type) [ParseError ε] (F : Parser τ ε α → Parser τ ε α) (n : Nat) (l : List τ),
    (below F n).parse l = if l.length < n then (fix F).parse l else .error ParseError.stuck l

end Keel.Spec
