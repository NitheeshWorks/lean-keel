# lean-keel

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

The keel of the verified FastAPI stack: the general theories that every other
`lean-*` repo instantiates, so a property is proved once and inherited, not
re-proved case by case.

| Module | Theory | The law, roughly |
|---|---|---|
| `Keel.Codec` | lawful encoder/decoder pairs, closed under combinators | `decode (encode a ++ rest) = some (a, rest)` |
| `Keel.Parse` | total parsers whose bind demands progress: no fuel, no `partial` | every parser terminates by construction |
| `Keel.Refine` | constraint language, refinement types `α ∣ c`, validation | `validate c x = .ok x ↔ c.holds x` |
| `Keel.Route` | first-match dispatch over templates with typed captures | `match (urlFor t v) = some v` |

Used by [lean-json](https://github.com/NitheeshWorks/lean-json),
[lean-multipart](https://github.com/NitheeshWorks/lean-multipart),
[lean-itsdangerous](https://github.com/NitheeshWorks/lean-itsdangerous),
[lean-markupsafe](https://github.com/NitheeshWorks/lean-markupsafe),
[lean-click](https://github.com/NitheeshWorks/lean-click),
[lean-jinja2](https://github.com/NitheeshWorks/lean-jinja2),
[lean-httpx](https://github.com/NitheeshWorks/lean-httpx),
[lean-pydantic](https://github.com/NitheeshWorks/lean-pydantic),
[lean-starlette](https://github.com/NitheeshWorks/lean-starlette) and
[lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi).

## What "verified" means here

* Every theorem is machine-checked. The gate (`scripts/Axioms.lean`) fails on
  any declaration that reaches an axiom beyond `propext`, `Quot.sound` and
  `Classical.choice`, and on any `partial`, `unsafe`, `implemented_by` or
  `extern` definition.
* Laws are stated once, on the abstraction, as equations or `↔` facts. Each
  instance in a downstream repo gets them for free.

## Getting started

```
lake build            # library and proofs
lake exe props        # property tests
scripts/check.sh      # the whole gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0`.

## License

MIT, see [LICENSE](LICENSE).
