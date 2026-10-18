import Keel.Proofs.Route
import Keel.RepoImpl.Convertors
import Keel.APIs.Parse

/-!
# APIs: compiling templates

`PathTemplate.compile` reads starlette's template syntax, `/items/{item_id}`
and `/items/{item_id:int}`, with the convertors of a registry (the built-ins
by default), and rejects unknown convertors and duplicated names with
starlette's messages. A `{` that does not start a well-formed parameter is
literal text, as in starlette's `PARAM_REGEX`.

`path% "/items/{item_id:int}"` does the same at elaboration time, so the
template's capture types are known to the type checker:
`(path% "/items/{item_id:int}").match "/items/42" : Option (Nat × Unit)`.

The template reader is itself a `Keel.Parse` parser.
-/

namespace Keel

namespace PathTemplate

/-- A piece of template syntax: one literal character, or a parameter with
its convertor's name. -/
inductive RawPiece where
  | char (c : Char)
  | param (name : String) (conv : String)
  deriving Repr, DecidableEq

open Parser in
/-- An identifier: `[a-zA-Z_][a-zA-Z0-9_]*`. -/
def identP : Parser Char Parse.Error String := do
  let c ← satisfy fun c => c.isAlpha || c == '_'
  let cs ← takeWhile fun c => c.isAlphanum || c == '_'
  pure (String.ofList (c :: cs))

open Parser in
/-- A parameter `{name}` or `{name:conv}`. -/
def paramP : Parser Char Parse.Error RawPiece := attempt do
  let _ ← token '{'
  let n ← identP
  let conv ← optional (token ':' *> identP)
  let _ ← token '}'
  pure (.param n (conv.getD "str"))

open Parser in
/-- Template syntax: parameters and literal characters. -/
def rawP : Parser Char Parse.Error (List RawPiece) := many (paramP <|> (RawPiece.char <$> next))

/-- Read template syntax. Every string reads (a stray `{` is literal). -/
def readRaw (s : String) : List RawPiece :=
  match rawP.parse s.toList with
  | .ok ps _ => ps
  | .error _ _ => s.toList.map .char

/-- Literal characters merged into literal runs: `(text, none)` or
`(name, some conv)`. -/
def mergeRaw : List RawPiece → List (List Char ⊕ (String × String))
  | [] => []
  | .char c :: ps =>
    match mergeRaw ps with
    | .inl l :: rest => .inl (c :: l) :: rest
    | rest => .inl [c] :: rest
  | .param n c :: ps => .inr (n, c) :: mergeRaw ps

/-- The names that occur more than once, sorted. -/
def duplicates (names : List String) : List String :=
  (names.filter fun n => names.count n > 1).eraseDups.mergeSort (· ≤ ·)

/-- Compile a template with the convertors of `registry` (starlette's
`compile_path`, without the regular expression). -/
def compile (s : String) (registry : List Convertor := Convertor.builtin) :
    Except String PathTemplate := do
  let parts := mergeRaw (readRaw s)
  let pieces ← parts.mapM fun
    | .inl l => pure (Piece.lit l)
    | .inr (n, cname) =>
      match registry.find? (·.name == cname) with
      | some c => pure (Piece.cap n c)
      | none => throw s!"Unknown path convertor '{cname}'"
  let dups := duplicates (names pieces)
  if dups.isEmpty then pure ⟨pieces⟩
  else
    let ending := if dups.length > 1 then "s" else ""
    throw s!"Duplicated param name{ending} {", ".intercalate dups} at path {s}"

end PathTemplate

open Lean in
/-- `path% "/items/{item_id:int}"`: a template compiled at elaboration time
with the built-in convertors, so its capture types are known statically. -/
syntax (name := pathTemplateLit) "path% " str : term

open Lean in
macro_rules
  | `(path% $s:str) => do
    let src := s.getString
    let parts := PathTemplate.mergeRaw (PathTemplate.readRaw src)
    let dups := PathTemplate.duplicates (parts.filterMap fun | .inr (n, _) => some n | .inl _ => none)
    unless dups.isEmpty do
      Macro.throwError s!"Duplicated param name(s) {", ".intercalate dups} at path {src}"
    let pieces ← parts.mapM fun
      | .inl l => `(Piece.lit $(quote (String.ofList l)).toList)
      | .inr (n, c) =>
        if ["str", "path", "int", "float", "uuid"].contains c then
          `(Piece.cap $(quote n) $(mkIdent (`Keel.Convertor ++ c.toName)))
        else Macro.throwError s!"Unknown path convertor '{c}'"
    `((⟨[$(pieces.toArray),*]⟩ : PathTemplate))

namespace Convertor

/-! ## Canonical texts -/

theorem str_canonical (t : List Char) : str.Canonical t := by
  intro x h
  have h' : String.ofList t = x := Option.some.inj h
  rw [← h']; show (String.ofList t).toList = t; simp

theorem path_canonical (t : List Char) : path.Canonical t := by
  intro x h
  have h' : String.ofList t = x := Option.some.inj h
  rw [← h']; show (String.ofList t).toList = t; simp

/-- **`int` accepts at most `maxIntDigits` digits**: CPython's
`int_max_str_digits`, checked on the text's length before any conversion. -/
theorem int_accepts_iff (t : List Char) :
    int.accepts t = true ↔ t ≠ [] ∧ t.length ≤ maxIntDigits ∧ ∀ c ∈ t, c.isDigit = true := by
  simp [and_assoc]

/-- An `int` text is canonical exactly when it is the shortest decimal of its
value: no leading zeros. -/
theorem int_canonical_iff (t : List Char) : int.Canonical t ↔ Codec.decimal (Codec.digitsValue t) = t := by
  simp [Canonical, int]

end Convertor

end Keel
