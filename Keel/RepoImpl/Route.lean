import Keel.DataTypes.Route

/-!
# Routing: matching, rendering, dispatch

* `PathTemplate.split` finds the capture texts of a path with starlette's
  regular-expression semantics: literals match exactly, and each capture
  takes the longest text its convertor accepts for which the rest of the
  template still matches (greedy, with backtracking). It is total: each
  capture tries finitely many prefix lengths, and the recursion is on the
  pieces.
* `PathTemplate.match` converts the texts; `urlFor` renders values back
  (starlette's `url_path_for` on one route).
* `dispatch` is first-match over any list of routes with a three-way match,
  and `Router.resolve` is starlette's `Router` decision: the first full match,
  else `405` with the first partial match's methods, else `404`.
-/

namespace Keel

namespace PathTemplate

/-- The path that the capture texts spell out, in order of the captures. -/
def urlTexts : List Piece → List (List Char) → List Char
  | [], _ => []
  | .lit l :: ps, ts => l ++ urlTexts ps ts
  | .cap _ _ :: ps, t :: ts => t ++ urlTexts ps ts
  | .cap _ _ :: ps, [] => urlTexts ps []

/-- The texts of the values, in order. -/
def renderArgs : (ps : List Piece) → Args ps → List (List Char)
  | [], _ => []
  | .lit _ :: ps, v => renderArgs ps v
  | .cap _ c :: ps, (x, v) => c.render x :: renderArgs ps v

/-- The first `some` among `f n, f (n - 1), …, f 0`. -/
def firstDown {β : Type} (f : Nat → Option β) : Nat → Option β
  | 0 => f 0
  | n + 1 =>
    match f (n + 1) with
    | some b => some b
    | none => firstDown f n

/-- The capture texts of a path, greedily, as a regular expression would
find them. -/
def split : List Piece → List Char → Option (List (List Char))
  | [], s => if s = [] then some [] else none
  | .lit l :: ps, s => if l <+: s then split ps (s.drop l.length) else none
  | .cap _ c :: ps, s =>
    firstDown (fun k =>
      if c.accepts (s.take k) then (split ps (s.drop k)).map (s.take k :: ·) else none)
      s.length

/-- Convert the capture texts, in order. -/
def convert : (ps : List Piece) → List (List Char) → Option (Args ps)
  | [], [] => some ()
  | [], _ :: _ => none
  | .lit _ :: ps, ts => convert ps ts
  | .cap _ _ :: _, [] => none
  | .cap _ c :: ps, t :: ts =>
    match c.parse t, convert ps ts with
    | some x, some v => some (x, v)
    | _, _ => none

/-- Match a path given as characters. -/
def matchPieces (ps : List Piece) (s : List Char) : Option (Args ps) := (split ps s).bind (convert ps)

/-- **Match** a path against the template: the converted captures, if it
matches. -/
def «match» (t : PathTemplate) (path : String) : Option (Args t.pieces) :=
  matchPieces t.pieces path.toList

/-- **The URL** of the template for the given values. -/
def urlFor (t : PathTemplate) (v : Args t.pieces) : String :=
  String.ofList (urlTexts t.pieces (renderArgs t.pieces v))

/-- Every value is one its convertor can render. -/
def ArgsValid : (ps : List Piece) → Args ps → Prop
  | [], _ => True
  | .lit _ :: ps, v => ArgsValid ps v
  | .cap _ c :: ps, (x, v) => c.Valid x ∧ ArgsValid ps v

/-- Every text is one its convertor accepts, one text per capture. -/
def TextsAccepted : List Piece → List (List Char) → Prop
  | [], ts => ts = []
  | .lit _ :: ps, ts => TextsAccepted ps ts
  | .cap _ _ :: _, [] => False
  | .cap _ c :: ps, t :: ts => c.accepts t = true ∧ TextsAccepted ps ts

/-- A text is canonical for a convertor when it is the rendering of what it
converts to: `7` for an `int`, not `007`. -/
def _root_.Keel.Convertor.Canonical (c : Convertor) (t : List Char) : Prop := ∀ x, c.parse t = some x → c.render x = t

/-- Every capture text is canonical. -/
def TextsCanonical : List Piece → List (List Char) → Prop
  | [], _ => True
  | .lit _ :: ps, ts => TextsCanonical ps ts
  | .cap _ _ :: _, [] => True
  | .cap _ c :: ps, t :: ts => c.Canonical t ∧ TextsCanonical ps ts

/-- A path is in canonical form for the template: the texts it captures are
canonical. -/
def Canonical (t : PathTemplate) (path : String) : Prop :=
  ∀ ts, split t.pieces path.toList = some ts → TextsCanonical t.pieces ts

/-- Segment-aligned templates: every capture is the last piece, or is
followed by a literal that starts with `/` and uses a convertor that never
accepts `/`. Such a capture is a whole path segment (or the tail of the path),
so matching is unambiguous. `/items/{id:int}`, `/users/{u}/posts/{p}` and
`/files/{rest:path}` are aligned; `/files/{name}.{ext}` is not. -/
def aligned : List Piece → Bool
  | [] => true
  | .lit _ :: ps => aligned ps
  | [.cap _ _] => true
  | .cap _ c :: .lit l :: ps => c.segment && l.head? == some '/' && aligned (.lit l :: ps)
  | .cap _ _ :: .cap _ _ :: _ => false

/-- The template is segment-aligned. -/
abbrev Aligned (t : PathTemplate) : Prop := aligned t.pieces = true

/-- The names of the captures. -/
def names : List Piece → List String
  | [] => []
  | .lit _ :: ps => names ps
  | .cap n _ :: ps => n :: names ps

/-- The captured values, by name, as text (starlette's `path_params`, rendered). -/
def namedTexts : (ps : List Piece) → Args ps → List (String × String)
  | [], _ => []
  | .lit _ :: ps, v => namedTexts ps v
  | .cap n c :: ps, (x, v) => (n, String.ofList (c.render x)) :: namedTexts ps v

end PathTemplate

/-! ## First-match dispatch -/

namespace Match

variable {β : Type}

/-- A full match. -/
def IsFull : Match β → Prop
  | .full _ => True
  | _ => False

instance (m : Match β) : Decidable m.IsFull := by
  cases m <;> simp only [IsFull] <;> infer_instance

/-- Whether a match is partial. -/
def isPartial : Match β → Bool
  | .partial => true
  | _ => false

theorem isPartial_iff (m : Match β) : m.isPartial = true ↔ m = .partial := by
  cases m <;> simp [isPartial]

end Match

/-- **First-match dispatch**: the first route that matches fully; if none
does, the first that matches partially; otherwise none. A partial match does
not stop the search for a full one. -/
def dispatch.{u} {ρ : Type u} {β : ρ → Type} (m : (r : ρ) → Match (β r)) : List ρ → Outcome ρ β
  | [] => .none
  | r :: rs =>
    match m r with
    | .full b => .found r b
    | .partial =>
      match dispatch m rs with
      | .found r' b => .found r' b
      | _ => .partial r
    | .none => dispatch m rs

/-! ## HTTP routes -/

namespace Route

variable {α : Type}

/-- Whether the route allows the method (a route without methods allows
every method). -/
def allows (r : Route α) (method : String) : Bool :=
  match r.methods with
  | none => true
  | some ms => ms.contains method

/-- How the route matches a request (starlette's `Route.matches`). -/
def «matches» (r : Route α) (method path : String) : Match (Args r.path.pieces) :=
  match r.path.match path with
  | none => .none
  | some v => if r.allows method then .full v else .partial

end Route

/-- Which methods a `405` lists in `Allow`. -/
inductive AllowPolicy where
  /-- The methods of the first route that matched the path: starlette's
  behaviour (recorded upstream as UP-027). -/
  | firstPartial
  /-- Every method of every route that matched the path, once each, in route
  order and then each route's method order. -/
  | unionOfPartials
  deriving DecidableEq, Repr, Inhabited

/-- The list without repeats, keeping first occurrences. -/
def dedup : List String → List String
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· != x)

/-- What the router does with a request. -/
inductive Resolution (α : Type) : Type 1 where
  /-- Run this route's endpoint with these captured values. -/
  | found (r : Route α) (args : Args r.path.pieces)
  /-- `405 Method Not Allowed`: the first route that matched the path, and the
  methods for `Allow`. -/
  | methodNotAllowed (r : Route α) (allow : List String)
  /-- `404 Not Found`. -/
  | notFound

/-- The methods of every route that matches the path, once each. -/
def Router.partialMethods {α : Type} (routes : List (Route α)) (method path : String) : List String :=
  dedup ((routes.filter fun r => (r.matches method path).isPartial).flatMap (·.methods.getD []))

/-- **The router**: starlette's `Router` decision for a method and a path; the
`Allow` list of a `405` follows `policy`. -/
def Router.resolve {α : Type} (routes : List (Route α)) (method path : String)
    (policy : AllowPolicy := .firstPartial) : Resolution α :=
  match dispatch (fun (r : Route α) => r.matches method path) routes with
  | .found r v => .found r v
  | .partial r =>
    .methodNotAllowed r
      (match policy with
       | .firstPartial => r.methods.getD []
       | .unionOfPartials => Router.partialMethods routes method path)
  | .none => .notFound

end Keel
