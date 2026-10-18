import Keel

/-!
# Example: a total recursive parser

Nested lists of naturals, `[1,[2,3],[]]`, parsed by a recursive parser built
with `Parser.fixDepth`: it is total by construction (no fuel, no `partial`),
and no input can drive it deeper than 256 nested lists, so it is safe on
untrusted input. The same parser runs on a `ByteArray`, an `Array` or a
`String`.

Inherits: totality (the type), `fixDepth_ok` (whenever the bounded parser
succeeds, it gives the unbounded `fix`'s result, because the body passes
failures on: `body_monotone`, proved by `approx`), and
`parse_fixDepth_zero` (past the bound, `depthExceeded`).
-/

namespace Examples.NestedLists

open Keel Parser

inductive Tree where
  | leaf (n : Nat)
  | node (ts : List Tree)

/-- The canonical text of a tree. -/
def Tree.render : Tree → List Char
  | .leaf n => Codec.decimal n
  | .node ts => '[' :: renderAll ts ++ [']']
where
  renderAll : List Tree → List Char
    | [] => []
    | [t] => t.render
    | t :: ts => t.render ++ ',' :: renderAll ts

/-- One level of the grammar: a number, or a bracketed list of trees. -/
def body (self : Parser Char Parse.Error Tree) : Parser Char Parse.Error Tree :=
  (.leaf <$> Codec.nat.parser) <|> (.node <$> (token '[' *> sepBy self (token ',') <* token ']'))

/-- The parser: at most 256 nested lists. -/
def tree : Parser Char Parse.Error Tree := fixDepth 256 body

/-- The body does not swallow failures that consumed input. -/
theorem body_monotone : Monotone body := fun p q h => by unfold body; approx

/-- **The bound changes nothing when the parse succeeds.** -/
theorem tree_ok {l r : List Char} {t : Tree} (h : tree.parse l = .ok t r) :
    (fix body).parse l = .ok t r :=
  fixDepth_ok body_monotone h

/-- On short inputs the two are the same parser outright. -/
theorem tree_eq_fix {l : List Char} (h : l.length < 256) : tree.parse l = (fix body).parse l :=
  fixDepth_eq_fix body 256 l h

/-! ## Concrete facts, checked by the kernel -/

example : (tree.parse "[1,[2,3],[]]".toList).map Tree.render = .ok "[1,[2,3],[]]".toList [] := by
  decide +kernel

/-- A bound of one nesting level rejects two, with `depthExceeded`. -/
example : ((fixDepth 1 body).parse "[[1]]".toList).map Tree.render = .error .depthExceeded "1]]".toList := by
  decide +kernel

/-! ## Running it -/

def run : IO Unit := do
  match tree.parseString "[1,[2,3],[]]" with
  | .ok ⟨t, _⟩ => IO.println s!"parsed: {String.ofList t.render}"
  | .error (e, p) => IO.println s!"error {repr e} at {p}"
  -- A million nested brackets: a clean error, not a stack overflow.
  let deep := (List.replicate 1000000 '[' ++ List.replicate 1000000 ']').toArray
  match tree.runFrom deep 0 with
  | .ok _ => IO.println "deep: parsed"
  | .error (e, p) => IO.println s!"deep: {repr e} at {p}"

end Examples.NestedLists
