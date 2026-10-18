# Contributing to lean-keel

`README.md` covers usage and lists what is proved. This file covers the
architecture, the verification rules, the decisions behind each theory, and
the deviations from starlette, and is the document to keep current when the
code changes.

## Architecture

Four theories, each one module that downstream repos import:

| Module | DataTypes | RepoImpl | Proofs | APIs |
|---|---|---|---|---|
| `Keel.Parse` | `Input.lean` (buffers), `Parse.lean` (`Result`, `Reply`, `ParseError`, `Parser`, `Parser.parse`) | `Parse.lean` (combinators with their invariant proofs) | `Parse.lean` (the `parse_*` laws) | `Parse.lean` (`runFrom`, `parseAll`, `parseBytes`, `parseString`) |
| `Keel.Codec` | `Codec.lean` (`Codec`, `Incomparable`, `Avoids`) | `Codec.lean` (combinators, each proving its law), `CodecBasic.lean` (`nat`, `natBE`, `string`, `bytes`) | `Codec.lean` (`*_lawful`, simp lemmas for side conditions) | `Codec.lean` (bytes and strings, `Literal`, `Codable`) |
| `Keel.Refine` | `Refine.lean` (`Constraint`, classes, `Loc`, `Located`, `Refine.Error`) | `Refine.lean` (`holds`, decision, `validate`, `Validator`, `α ∣ c` notation) | `Refine.lean` | `Refine.lean` (`refine`, `Validator.ofConstraint`) |
| `Keel.Route` | `Route.lean` (`Convertor`, `Piece`, `PathTemplate`, `Args`, `Match`, `Outcome`, `Route`) | `Route.lean` (`split`, `match`, `urlFor`, `dispatch`, `Router.resolve`), `Convertors.lean` | `Route.lean` | `Route.lean` (`compile`, `path%`, canonical texts) |

`Specifications/<Theory>.lean` states each headline law as a `Prop`, and
`Proofs/Verified.lean` has one `Verified<Theory>` structure per theory whose
fields are those `Prop`s: a law without a proof is a compile error there.

Layers import only those below them. Definitions whose type carries an
invariant (a `Parser`, a `Codec`, a `Convertor`) prove it where they are
defined; the laws users cite live in `Proofs/`.

## Verification <a name="verification"></a>

* **Totality without fuel.** Nothing under `Keel/` is `partial`, and nothing
  takes a fuel argument. A `Parser` carries two invariants as fields:
  translation invariance (`run s i` is the run at `0` on the tokens from `i`,
  shifted) and in-bounds positions. Together they mean that a step that
  moved has strictly fewer tokens left, which is the well-founded measure of
  `many`, and of `below`/`fix`, whose recursive handle runs only on strictly
  fewer tokens than the call that made it (and reports `ParseError.stuck`
  otherwise, which happens only for a left-recursive grammar). Lean's
  well-founded recursion compiles to plain recursion; the measure costs
  nothing at run time.
* **Bounded stack.** Totality is not enough for a server: `fix` recurses as
  deep as the input nests, so 10^6 nested brackets exhaust a native stack.
  `fixDepth max F` is structural on `max`, so no input drives it deeper than
  `max` nested calls; past the bound it fails with `depthExceeded`. Parsers of
  untrusted input use `fixDepth`. The loops (`many`, `takeWhile`, `manyTill`,
  `sepBy`) are accumulator loops in constant stack; `tests/Props.lean` probes
  both natively (10^6 nesting, 10^7 width).
* **Laws on lists, code on arrays.** Every parser law is an equation for
  `Parser.parse : List τ → Reply τ ε α`. `Parser.ext` says a parser is its
  list meaning, and `Parser.run_eq_of_parse` transports a list fact to any
  buffer (`ByteArray`, `Array`, `Slice`). Proofs never index a byte array.
* **Laws as types.** A `Codec` contains its round-trip law, a `Convertor` its
  `parse_render`, a refined value its proof. Combinators prove the law once;
  every codec built from them is lawful without a proof of its own.
* **Honest side conditions.** A codec's law is conditional on `valid a` (the
  values it round-trips) and `follow rest` (the continuations its decoder
  tolerates: `True` for prefix-free codecs, "no digit next" for a decimal).
  Each combinator states its conditions from its parts', and simp lemmas
  (`*_valid`, `*_follow`) reduce them for concrete codecs, so `simp` and then
  `decide` discharge them. `Codec.refine` moves a condition into the type.
* **The gate.** `scripts/check.sh` runs what CI runs: build, the verification
  gate (`scripts/Axioms.lean`: every declaration under `Keel` reaches only
  `propext`, `Quot.sound` and `Classical.choice`, and none is `partial`,
  `unsafe`, `implemented_by` or `extern`; `scripts/gate-allow.txt` is empty),
  `lake exe props`, `lake exe conformance`, the traceability check, and with
  `--pbt` the plausible suite.

### Tested, not proved

Nothing. Every behaviour the card names is proved; `tests/Props.lean`
and `tests/pbt/` re-run the laws on the executable buffers as smoke tests of
the definitions, and `tests/Conformance.lean` re-expresses starlette's
routing tests.

## Decisions

* **Parse: committed choice.** `p <|> q` tries `q` only if `p` failed without
  consuming, as in Parsec and Lean's `Std.Internal.Parsec`; `attempt` makes a
  failure non-consuming. This keeps error positions precise (a JSON array
  error is reported at the bad element, not at the `[`). `lit` is atomic.
* **Parse: errors are positional.** A `Result` carries the position of an
  error, so downstream error types need no position field. The library's own
  failures are the three kinds of `ParseError ε` (`eof`, `unexpected`,
  `stuck`), which any error type can provide; `Parse.Error` is ready-made.
* **Parse: values are position-independent.** Translation invariance rules out
  a "current position" parser; positions appear only in `Result` and
  `runFrom`. This is what makes the list semantics complete.
* **Parse: a depth failure is a consumed failure.** `fixDepth` past its bound
  fails through `failAhead`, reported one token past the call, so committed
  choice does not mistake it for "this alternative does not apply" (otherwise
  `sepBy self sep <|> pure []` would swallow it and a later token would be
  blamed). `ParseError.depthExceeded` defaults to `stuck` for error types
  that do not distinguish it.
* **Codec: the decoder is a `Keel.Parse` parser**, polymorphic in the error
  type, so a codec composes with hand-written parsers and runs on any buffer.
  `delimited` and `lengthPrefixed` confine the inner decoder with
  `Parser.isolate`, a `Slice` of the same buffer: no copying.
* **Refine: first failure for `and`.** A conjunction reports the first failing
  side, as pydantic-core reports the first violated constraint of a field;
  `Validator.both` and `each` report every failing part, as a model reports
  every failing field. `or` reports both sides' errors.
* **Refine: patterns are supplied.** `Pattern` is a source string and a
  matcher. Keel fixes no regular-expression language; lean-pydantic supplies a
  verified matcher with its source, so the schema and the check cannot drift.
* **Refine: `α ∣ c` coexists with `Dvd`.** The notation is scoped to
  `open Keel`, has priority over divisibility, and parses the constraint
  language as its own syntax category whose atoms are the constraint names as
  non-reserved keywords. So `String ∣ maxLength 50 ∧ minLength 3` is the
  conjunction, `Nat ∣ le 100` elaborates to `Refined Nat (Constraint.le 100)`
  with no stray auto-bound implicits, and `3 ∣ n` or `k ∣ n ∧ k ∣ m` (no
  constraint name after `∣`) still mean divisibility. A constraint held in a
  variable is written `Refined α c`.
* **Refine: literals check themselves.** A numeral or string literal whose
  expected type is `Refined α c` elaborates to `⟨lit, by decide⟩`, so
  defaults read `discount : Nat ∣ le 100 := 0` and calls read `pct 50`; an
  out-of-range literal is a compile error.
* **Refine: case-insensitive choices** use `oneOfBy norm choices` and
  `Constraint.pick`, which returns the first declared choice (click's
  behaviour), not the input.
* **Route: convertors are values.** A `Convertor` is a record with its laws,
  so a downstream repo registers its own (starlette's
  `register_url_convertor`) and passes a registry to `PathTemplate.compile`.
* **Route: regex semantics without regexes.** A capture takes the longest
  text its convertor accepts for which the rest of the template still matches
  (greedy with backtracking), then all captures are converted, as starlette
  matches its compiled regex and then calls `convert`. For the built-in
  convertors this equals Python's backtracking order.
* **Route: the `Allow` policy is a parameter** (orchestrator decision).
  `.firstPartial`, the default, is starlette's behaviour (the first partially
  matching route's methods, UP-027); `.unionOfPartials` is the deduplicated
  union in route order. lean-starlette chooses.

## Deviations from starlette

| Behaviour | starlette | Keel | Ledger |
|---|---|---|---|
| `float` captures | IEEE doubles, rendered with `"%0.20f"` and stripped, so `0.1` renders as `0.10000000000000000555` | exact decimals (`Convertor.Fixed`), rendered with trailing zeros dropped | UP-029 |
| End of path | the regex ends in `$`, which also matches before a trailing newline (`/int/5\n` routes with `5`) | the whole path must match | UP-030 |
| `url_path_for` | substitutes `{name}` by `str.replace` one parameter after another, so a value containing another parameter's placeholder is rewritten | each value is rendered once, verbatim, from the template pieces | UP-031 |
| `Allow` | the first partial route's methods, `", ".join` of a set: hash-seed dependent | an `AllowPolicy`: that route's methods in declaration order (default), or the union of all partial routes' methods | UP-027 |

## Tests

* `tests/Props.lean`: seeded properties, one or more per combinator, running
  on `ByteArray`, `Array` and `String` buffers; under a second.
* `tests/Conformance.lean`: starlette's routing and convertor tests that
  concern templates and dispatch, each naming its upstream test.
* `tests/pbt/`: a separate Lake package, the one place an external dependency
  (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links each law to the Lean symbols and tests that
realise it, and records the deviations and exclusions. CI fails if a
registered symbol does not resolve or a test path is missing.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the library depends only on
  Lean core.
* Choose the definition that suits `simp` and `omega` over a prettier one with
  a harder proof (capture texts are a plain list for this reason; character
  classes are stated on `Char.toNat`).
* API stability: downstream repos build on these modules. A breaking change
  is announced on the kanban card with `API CHANGE:`.
