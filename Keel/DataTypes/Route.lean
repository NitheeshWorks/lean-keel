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

A convertor also carries an `Acceptor`: its language as a one-pass
recogniser (a deterministic automaton that may stop early), which is how a
capture finds every accepted prefix of a path in one left-to-right pass. The
law `acceptor_accepts` says it recognises exactly `accepts`. A convertor that
gives none gets `Acceptor.ofTest`, correct for any test but quadratic in the
text it scans; the built-ins give linear ones.

`Match` is starlette's three-way match result (`full`, `partial`: the path
matched but not the method, `none`), and `Outcome` is the result of
first-match dispatch over a list of routes.
-/

namespace Keel

/-- A one-pass recogniser: a deterministic automaton over characters. `step`
answers `none` when no extension of what was read is accepted, so a scan can
stop there (a segment convertor stops at the first `/`, `int` after its
digit limit). -/
structure Acceptor where
  /-- What the automaton remembers of the text read so far. -/
  State : Type
  start : State
  step : State → Char → Option State
  /-- Whether the text read so far is accepted. -/
  final : State → Bool

namespace Acceptor

/-- The state after reading a text, `none` once the automaton has stopped. -/
def run (a : Acceptor) : a.State → List Char → Option a.State
  | q, [] => some q
  | q, c :: cs => (a.step q c).bind (a.run · cs)

/-- The texts the automaton accepts. -/
def accepts (a : Acceptor) (t : List Char) : Bool := (a.run a.start t).any a.final

/-- The recogniser for any test: it remembers the text read (reversed) and
tests it. Correct for every test, but each test reads the whole prefix again:
a convertor gives its own acceptor to match in linear time. -/
@[reducible] def ofTest (test : List Char → Bool) : Acceptor where
  State := List Char
  start := []
  step q c := some (c :: q)
  final q := test q.reverse

theorem ofTest_run (test : List Char → Bool) :
    ∀ (q t : List Char), (ofTest test).run q t = some (t.reverse ++ q)
  | q, [] => rfl
  | q, c :: cs => by
    show (ofTest test).run (c :: q) cs = _
    rw [ofTest_run test]; simp

theorem ofTest_accepts (test : List Char → Bool) (t : List Char) :
    (ofTest test).accepts t = test t := by
  show ((ofTest test).run [] t).any (fun q => test q.reverse) = test t
  simp [ofTest_run, Option.any]

/-- The recogniser for a test that accepts only texts of at most `n`
characters: it stops after `n`, so a scan of a long text reads at most `n`
characters. -/
@[reducible] def ofBounded (test : List Char → Bool) (n : Nat) : Acceptor where
  State := List Char
  start := []
  step q c := if q.length < n then some (c :: q) else none
  final q := test q.reverse

theorem ofBounded_run (test : List Char → Bool) (n : Nat) :
    ∀ (q t : List Char), q.length ≤ n → (ofBounded test n).run q t =
      if q.length + t.length ≤ n then some (t.reverse ++ q) else none
  | q, [], hq => by simp only [run]; simp [hq]
  | q, c :: cs, hq => by
    show ((if q.length < n then some (c :: q) else none).bind fun q => (ofBounded test n).run q cs) = _
    by_cases h : q.length < n
    · simp only [h, ite_true, Option.bind_some]
      rw [ofBounded_run test n _ _ (by simp; omega)]
      simp only [ List.length_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
      congr 1; apply propext; omega
    · simp only [h, ite_false, Option.bind_none, List.length_cons]
      rw [ite_eq_right_iff.2]; intro; omega

theorem ofBounded_accepts (test : List Char → Bool) (n : Nat)
    (h : ∀ t, test t = true → t.length ≤ n) (t : List Char) :
    (ofBounded test n).accepts t = test t := by
  show ((ofBounded test n).run [] t).any (fun q => test q.reverse) = test t
  rw [ofBounded_run _ _ _ _ (Nat.zero_le _)]
  by_cases hl : t.length ≤ n
  · simp [hl, Option.any]
  · have : test t = false := by
      cases ht : test t
      · rfl
      · exact absurd (h t ht) hl
    simp [hl, this, Option.any]

end Acceptor

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
  /-- The language as a one-pass recogniser, for matching in linear time. -/
  acceptor : Acceptor := Acceptor.ofTest accepts
  acceptor_accepts : ∀ t, acceptor.accepts t = accepts t := by exact Acceptor.ofTest_accepts _

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
