import Keel.Parse
import Keel.Codec
import Keel.Proofs.Verified

/-!
# Keel

The shared theories of the verified FastAPI stack: lawful codecs, total
parsing, refinement and validation, and routing. Each states its laws once;
every lean-* repo instantiates them.

Each theory is one module (`Keel.Parse`, `Keel.Codec`, `Keel.Refine`,
`Keel.Route`), layered bottom to top (each layer imports only those below):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
