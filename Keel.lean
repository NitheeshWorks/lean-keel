import Keel.APIs
import Keel.Proofs.Verified

/-!
# Keel

The shared theories of the verified FastAPI stack: lawful codecs, total parsing,
refinement and validation, and routing. Each states its laws once; every lean-*
repo instantiates them.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
