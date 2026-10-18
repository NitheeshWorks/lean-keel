import Keel.Proofs.Parse
import Keel.Specifications.Parse

/-!
# The harness: one `Verified<Theory>` structure per theory

Each `Verified<Theory>` bundles a proof term for every headline property
`Specifications/<Theory>.lean` states. A specification with no proof is a
compile error the moment it needs a field here: no `Verified<Theory>` value
can be built without every proof in hand. If a stated specification turned
out false, its slot's type would flip to a refutation rather than being
dropped, so this file stays an honest map of what is verified.
-/

namespace Keel

/-- Total parsing: extensionality, the buffer bridge, and one law per
combinator. -/
structure VerifiedParse where
  ext : Spec.ParseExt
  runOfParse : Spec.RunOfParse
  bind : Spec.ParseBind
  orElse : Spec.ParseOrElse
  lit : Spec.ParseLit
  startsWith : Spec.ParseStartsWith
  many : Spec.ParseMany
  takeWhile : Spec.ParseTakeWhile
  fix : Spec.ParseFix
  below : Spec.ParseBelow

def theVerifiedParse : VerifiedParse where
  ext _ _ _ _ _ h := Parser.ext h
  runOfParse _ _ _ _ _ p _ _ _ _ h hi := p.run_eq_of_parse h hi
  bind _ _ _ _ := Parser.parse_bind
  orElse _ _ _ := Parser.parse_orElse
  lit _ _ _ _ := Parser.parse_lit
  startsWith _ _ _ _ := Parser.parse_startsWith
  many _ _ _ := Parser.parse_many
  takeWhile _ _ _ := Parser.parse_takeWhile
  fix _ _ _ _ := Parser.parse_fix
  below _ _ _ _ := Parser.parse_below

end Keel
