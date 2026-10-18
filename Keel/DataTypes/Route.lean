/-!
# Routing: convertors, templates, matches

A path template such as `/items/{item_id:int}` is a list of pieces: literal
text and typed captures. A capture's type is given by its *convertor*, which
is starlette's `Convertor` made lawful: the language of texts it accepts (the
convertor's regular expression, as a test), the conversion from text, the
rendering back, and the two laws that tie them together are fields.
Convertors are values, so a downstream repo registers new ones as starlette's
`register_url_convertor` does.

The values captured by a template have a type computed from its pieces,
`Args pieces`: a template's `match` and `urlFor` are typed by it, so a route's
handler receives, for `{item_id:int}`, a `Nat`.

`Match` is starlette's three-way match result (`full`, `partial`: the path
matched but not the method, `none`), and `Outcome` is the result of
first-match dispatch over a list of routes.
-/

namespace Keel

/-- A lawful path convertor. -/
structure Convertor where
  /-- The name used in templates: `str`, `int`, … -/
  name : String
  /-- The type of converted values. -/
  Val : Type
  /-- The texts the convertor matches (its regular expression, whole-text). -/
  accepts : List Char → Bool
  /-- The conversion of a matched text (`Convertor.convert`). -/
  parse : List Char → Option Val
  /-- The text of a value (`Convertor.to_string`). -/
  render : Val → List Char
  /-- The values `to_string` accepts. -/
  Valid : Val → Prop
  accepts_render : ∀ v, Valid v → accepts (render v) = true
  parse_render : ∀ v, Valid v → parse (render v) = some v
  /-- Whether accepted texts stay within one path segment (no `/`): true for
  every built-in convertor except `path`. -/
  segment : Bool
  segment_spec : segment = true → ∀ t, accepts t = true → '/' ∉ t

/-- A piece of a path template. -/
inductive Piece where
  | lit (text : List Char)
  | cap (name : String) (conv : Convertor)

/-- A path template: its pieces, in order. -/
structure PathTemplate where
  pieces : List Piece

/-- A value for every capture of the pieces, of a type chosen per convertor. -/
@[reducible] def ArgsOf (F : Convertor → Type) : List Piece → Type
  | [] => Unit
  | .lit _ :: ps => ArgsOf F ps
  | .cap _ c :: ps => F c × ArgsOf F ps

/-- The converted values of the captures. -/
abbrev Args (ps : List Piece) : Type := ArgsOf Convertor.Val ps


/-- How one route matches a request (starlette's `Match`). -/
inductive Match (β : Type) where
  /-- Path and method match, with the captured values. -/
  | full (b : β)
  /-- The path matches but the method does not. -/
  | «partial»
  /-- The path does not match. -/
  | none

/-- The result of first-match dispatch over routes of type `ρ`, the captured
values depending on the route. -/
inductive Outcome.{u, v} (ρ : Type u) (β : ρ → Type v) where
  /-- The first route that matched fully, with its values. -/
  | found (r : ρ) (b : β r)
  /-- No full match; the first route that matched partially. -/
  | «partial» (r : ρ)
  /-- No route matched the path. -/
  | none

/-- An HTTP route: a template, the methods it allows (`none` allows every
method), and an endpoint. -/
structure Route (α : Type) where
  path : PathTemplate
  methods : Option (List String) := none
  endpoint : α

end Keel
