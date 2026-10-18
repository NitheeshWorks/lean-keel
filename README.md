# lean-keel

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

The keel of the verified FastAPI stack: the general theories that every other
`lean-*` repo instantiates, so a property is proved once and inherited, not
re-proved case by case.

| Module | Theory | The law |
|---|---|---|
| `Keel.Parse` | total parsers over any token buffer: no fuel, no `partial` | `(p >>= f).parse l = (p.parse l).bind fun a r => (f a).parse r` |
| `Keel.Codec` | lawful encoder/decoder pairs, closed under combinators | `c.decode (c.encode a ++ rest) = some (a, rest)` |
| `Keel.Refine` | constraint language, refinement types `α ∣ c`, located validation | `c.validate x = .ok x ↔ c.holds x` |
| `Keel.Route` | typed path templates, first-match dispatch, 405 and 404 | `t.match (t.urlFor v) = some v` |

## Quickstart

```lean
import Keel
open Keel

-- Parse: a total recursive parser, depth-bounded so that no input can
-- exhaust the stack (past 512 levels it fails with `depthExceeded`). It runs
-- on a ByteArray, an Array or a String, and is reasoned about on lists.
inductive Tree where | leaf (n : Nat) | node (ts : List Tree)

open Parser in
def body (self : Parser Char Parse.Error Tree) : Parser Char Parse.Error Tree :=
  (do let ds ← many1 (satisfy Char.isDigit); pure (.leaf (Codec.digitsValue ds)))
  <|> (do let _ ← token '['; let ts ← sepBy self (token ','); let _ ← token ']'; pure (.node ts))

def tree : Parser Char Parse.Error Tree := Parser.fixDepth 512 body

-- The bound changes nothing when the parse succeeds: the body passes
-- failures on (`Monotone`, proved by `approx`), so `fixDepth_ok` applies.
theorem body_monotone : Parser.Monotone body := fun p q h => by unfold body; approx

example {l r : List Char} {t : Tree} (h : tree.parse l = .ok t r) : (Parser.fix body).parse l = .ok t r :=
  Parser.fixDepth_ok body_monotone h

#eval (tree.parseString "[1,[22,3],[]]").isOk   -- true: a value, with the proof it is the list meaning

-- Codec: built from combinators, lawful by construction.
def field : Codec UInt8 ByteArray := Codec.bytes
def headerCodec := Codec.delimited "\r\n" field |>.many

example (lines : List ByteArray) (h : Codec.ManyValid (Codec.delimited "\r\n" field) lines) :
    headerCodec.decode (headerCodec.encode lines) = some (lines, []) :=
  Codec.many_lawful _ h

-- Refine: constraints are types; a literal is checked where it is written.
structure Offer where
  price    : Int ∣ gt 0
  discount : Nat ∣ le 100 := 0

def search (q : Option (String ∣ maxLength 50 ∧ minLength 3) := none) : String :=
  (q.map (·.val)).getD ""

def pct (x : Nat ∣ le 100) : Nat := x.val
#eval pct 50                                  -- 50

#eval ((Constraint.gt (0 : Int)).refine (-1)).isOk   -- false: one error, `failed := gt 0`

-- Route: templates with typed captures, starlette's semantics.
abbrev item := path% "/items/{item_id:int}"
#eval item.match "/items/42"                 -- some (42, ())
example (n : Nat) : item.match (item.urlFor (n, ())) = some (n, ()) :=
  item.match_urlFor (by decide) _ ⟨trivial, trivial⟩
```

## Examples

`examples/` has one worked example per theory, each with the laws it
inherits proved for it (listed in `examples/MANIFEST.toml`; `lake exe
examples` runs them all):

| Example | Theory | What it shows |
|---|---|---|
| `HeaderCodec` | `Keel.Codec` | a length-prefixed header list built from combinators; `roundTrip` for every header list, the side conditions carried by the field types |
| `NestedLists` | `Keel.Parse` | a recursive parser with `fixDepth`; `tree_ok` (agrees with `fix` whenever it succeeds); 10^6 nesting fails with `depthExceeded` |
| `Offer` | `Keel.Refine` | STYLE.md's `Offer`, a literal default, validation with errors located under each field (`validate_errors_located`) |
| `Router` | `Keel.Route` | a router with a typed capture, both `Allow` policies, and `DELETE` on any item proved a 405 |

## What is proved

Every statement below is a Lean theorem about the public functions, checked by
the gate (`scripts/Axioms.lean`): only `propext`, `Quot.sound` and
`Classical.choice`, no `sorry`, no `partial`, no fuel. Each has a slot in
`Keel/Proofs/Verified.lean`.

### Keel.Parse

* **Every parser is total.** Not a theorem but the type: `many` and `fix`
  recurse well-founded on the number of tokens left, and a `Parser` carries
  the invariants (translation invariance, in-bounds positions) that make the
  measure decrease.
* **Parsers are their list meaning.** Two parsers that agree on every list
  are equal, and on any buffer a parser does what its list meaning says.
  `Parser.ext : (∀ l, p.parse l = q.parse l) → p = q`;
  `Parser.run_eq_of_parse : p.parse (Input.rest s i) = .ok a r → i ≤ Input.size s → p.run s i = .ok a (Input.size s - r.length)`.
* **Sequencing continues on what is left.**
  `Parser.parse_bind : (p >>= f).parse l = (p.parse l).bind fun a r => (f a).parse r`, and the parsers form a lawful monad.
* **Choice is committed.** `Parser.parse_orElse`: `q` runs only when `p` failed having consumed nothing.
* **Repetition unfolds once**, continuing only after a step that consumed: `Parser.parse_many`.
* **`takeWhile` is `List.takeWhile`.** `Parser.parse_takeWhile : (takeWhile f).parse l = .ok (l.takeWhile f) (l.dropWhile f)`.
* **Literals and lookahead.** `parse_lit : (lit l).parse (l ++ r) = .ok () r`;
  `parse_startsWith : (startsWith l).parse x = .ok (decide (l <+: x)) x`.
* **Confinement.** `parse_isolate_append : l.length = n → p.parse l = .ok a [] → (isolate n p).parse (l ++ r) = .ok a r`.
* **Bounded recursion** (the form for untrusted input). `fixDepth max F`
  never has more than `max` recursive calls active, by structural recursion on
  `max`, so its native stack depth is bounded whatever the input; past the
  bound it fails with `depthExceeded`, as a consumed failure no alternative
  can swallow. **Whenever it succeeds, it gives the unbounded fixpoint's
  result**, for a body that does not swallow failures that consumed input
  (`Parser.Monotone F`, which every combinator but `attempt` preserves; the
  `approx` tactic proves it for a body built from them):
  `fixDepth_ok : Monotone F → (fixDepth d F).parse l = .ok a r → (fix F).parse l = .ok a r`.
  More precisely `fixDepth_approx`: on every input it agrees with `fix F` or
  fails having consumed input. And `parse_fixDepth_zero : (fixDepth 0 F).parse (t :: l) = .error ParseError.depthExceeded l`,
  `parse_fixDepth_succ : (fixDepth (d + 1) F).parse l = (F (guarded l.length fun _ _ => fixDepth d F)).parse l`.
* **Unbounded recursion.** `parse_fix : (fix F).parse l = (F (below F l.length)).parse l` and
  `parse_below_of_lt : l.length < n → (below F n).parse l = (fix F).parse l`:
  the recursive handle is the fixpoint on every strictly shorter input. `fix`
  recurses as deep as the input nests, so it is not for untrusted input.

### Keel.Codec

* **The codec law, on any continuation.**
  `Codec.decode_encode : c.valid a → c.follow rest → c.decode (c.encode a ++ rest) = some (a, rest)`,
  and its forms on bytes and strings, run on the buffer itself:
  `decodeBytes_encodeBytes`, `decodeString_encodeString`.
* **Encoding is injective** on valid values: `Codec.encode_injective`.
* **Every combinator is lawful**: `seq_lawful`, `map_lawful`, `refine_lawful`,
  `sigma_lawful` (choice by a decoded tag), `sum_lawful_inl`/`inr` (choice by
  literal tags), `delimited_lawful`
  (`Avoids d (c.encode a) → (delimited d c).decode (c.encode a ++ d ++ r) = some (a, r)`),
  `lengthPrefixed_lawful`, `many_lawful`, `manyTill_lawful`.
* **Base codecs**: `nat_lawful` (decimal, before any non-digit) and
  `natBE_lawful` (big-endian, when the value fits).

### Keel.Refine

* **Validation is sound and complete.** `Constraint.validate_iff : c.validate x = .ok x ↔ c.holds x`.
* **A failure says why.** `validate_error_ne_nil : c.validate x = .error es → es ≠ []`.
* **Conjunction validates both.** `validate_and_iff : (c.and d).validate x = .ok x ↔ c.validate x = .ok x ∧ d.validate x = .ok x`.
* **Refinement.** `refine_ok_iff : (∃ y, c.refine x = .ok y) ↔ c.holds x`, the value carrying its proof.
* **Choices up to a normalisation** (click's case-insensitive `Choice`):
  `pick_ok_iff : (∃ c, pick norm cs x = .ok c ∧ c.val = v) ↔ cs.find? (fun c => decide (norm c = norm x)) = some v`,
  the first declared choice; `pick_isOk_iff` relates it to `oneOfBy norm cs`.
* **Error locations compose along paths.**
  `Validator.atPath_append : v.atPath (p ++ q) = (v.atPath q).atPath p` and
  `prefix_loc_atPath : (v.atPath p) x = .error es → ∀ e ∈ es, p <+: Located.loc e`.
* **Models.** `Refine.Issue` is one located error type for fields of any type;
  `Validator.field k get v` validates a field under its key, `Validator.check`
  a constraint (`check_ok_iff`, `loc_check`).
* **Lists and pairs.** `each_ok_iff : (each v) xs = .ok ys ↔ xs.mapM v = .ok ys`;
  `loc_each`: every error of `each` is under an element's index; `both_ok_iff`.

### Keel.Route

* **`match` inverts `urlFor`.**
  `PathTemplate.match_urlFor : t.Aligned → ArgsValid t.pieces v → t.match (t.urlFor v) = some v`,
  for segment-aligned templates (every capture is a whole segment or the tail).
* **`urlFor` inverts `match` on canonical paths.**
  `PathTemplate.urlFor_match : t.match path = some v → t.Canonical path → t.urlFor v = path`.
* **First match.** `dispatch_found_iff`: dispatch finds `r` exactly when `r`
  matches fully and no earlier route does; `Router.resolve_found_iff` for HTTP.
* **405 iff partial**, for either `Allow` policy. `Router.methodNotAllowed_iff`:
  the router answers 405 exactly when no route matches the method and the
  path, and some route matches the path.
* **The `Allow` list** follows an `AllowPolicy` argument (default
  `.firstPartial`). `methodNotAllowed_allow_first`: under `.firstPartial`
  (starlette's behaviour, UP-027) it is the methods of the first route that
  matched the path. `methodNotAllowed_allow_union`: under `.unionOfPartials`
  a method is listed exactly when some partially matching route lists it,
  each once (`Nodup`), in route order.
* **404 iff no path match.** `Router.notFound_iff : resolve rs method path = .notFound ↔ ∀ r ∈ rs, r.path.match path = none`.
* **Matching is linear in the path, and is the specification.** Each
  convertor carries an `Acceptor`, a one-pass automaton for its language
  (`acceptor_accepts : c.acceptor.accepts t = c.accepts t`); a capture finds
  all its accepted prefixes in one tail-recursive pass (`Acceptor.cuts`), which
  stops where the automaton does (`str`, `int`, `float`, `uuid` at the first
  `/`; `int` past 4300 digits; `uuid` past 37 characters). Compiled code runs
  `splitFast` by `@[csimp]` on `split_eq_splitFast : split ps s = splitFast ps s`,
  so every law above, stated on `split`, holds of the code that runs. Recursion
  depth is the number of template pieces, not the path length.
  `lake exe bench` times 65535-character non-matching paths for each shape
  (`/s/{a}/x`, `/p/{a:path}/end`, `/u/{a}-{b}`, and int, float and uuid
  captures) against a 100 ms bound; each takes a few milliseconds.
* **`int` takes at most 4300 digits** (CPython's `int_max_str_digits`),
  checked on the length before any conversion:
  `Convertor.int_accepts_iff : int.accepts t ↔ t ≠ [] ∧ t.length ≤ maxIntDigits ∧ ∀ c ∈ t, c.isDigit`.
  So `int.Valid n` is `n < 10 ^ maxIntDigits`, and 1 MiB of digits is
  rejected after reading 4301 of them.
* **Long decimals.** `decimal_csimp : decimal = decimalFast` (an accumulator,
  18 digits per division) and `digitsValue_csimp : digitsValue = digitsValueFast`
  (digit runs joined pairwise, about log₂ n passes): compiled code is
  subquadratic and has no recursion depth on the number of digits.

## Using Keel from a lean-* repo

Add the requirement to `lakefile.toml` and `lake update Keel`:

```toml
[[require]]
name = "Keel"
git = "https://github.com/NitheeshWorks/lean-keel"
rev = "main"
```

| Repo | Use | Instead of |
|---|---|---|
| lean-json | `Parser UInt8 ParseErr Json` with the depth-bounded `fixDepth` for values (jiter's recursion limit as `max`, `depthExceeded` mapped to `recursionLimitExceeded` in the `ParseError ParseErr` instance), `parse_*` laws, `fixDepth_ok` (with `Monotone` for the value body, by `approx`), `Parser.run_eq_of_parse`; `Codec.nat`/`Codec.lit` for leaves | the fuel arguments, `parse_fuel_mono`, `parse_fuel_enough`, `step_progress`, the `Spec.At` byte lemmas |
| lean-multipart | `Codec.delimited` (boundaries: `Avoids`), `Codec.many`/`manyTill`, `Parser.takeWhile` | hand-rolled `findBoundary` and `_ext` round trips |
| lean-itsdangerous | `Codec.delimited` with `avoids_of_head_not_mem` for the separator; `Codec.natBE` for timestamps | `splitFirst_append`, `rsplit_append`, `bytesToInt_intToBytes` |
| lean-click | `Int ∣ ge lo ∧ le hi` (IntRange), `String ∣ oneOf cs` (case-sensitive `Choice`), `Constraint.pick normChoice cs` with `pick_ok_iff` (case-insensitive `Choice`: the first declared choice, as `find?`), `Constraint.validate_iff`; `dispatch` for groups | `IntBounds.contains` proofs, `choice_in_set`, `group_dispatch_first_match` |
| lean-pydantic | `Constraint`, `α ∣ c`, `Validator` with `Located` for `ValidationError`, `loc_atPath`; supply a `Pattern` from the verified regex | its own `Constraint`/`Satisfies`/`validate_sound`/`validate_complete`/`validate_loc_prefix` |
| lean-starlette | `PathTemplate`, `Convertor`, `path%`, `Router.resolve` with an `AllowPolicy`, `match_urlFor`, `methodNotAllowed_iff`, `methodNotAllowed_allow_first`/`_union` | its own `compile_match_url_path_for`, `route_first_match`, `partial_iff_405` |

## Getting started

```
lake build            # library, proofs, test executables
lake exe props        # property tests
lake exe conformance  # starlette routing cases
lake exe examples     # the worked examples
scripts/check.sh      # the whole gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0`. See `CONTRIBUTING.md` for the
architecture and the deviations from starlette.

## License

MIT, see [LICENSE](LICENSE).
