import Keel.Proofs.Parse
import Keel.Specifications.Parse
import Keel.Specifications.Codec

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

/-- Lawful codecs: the general law and its forms, and one law per
combinator. -/
structure VerifiedCodec where
  law : Spec.CodecLaw
  encodeInjective : Spec.EncodeInjective
  bytes : Spec.BytesLaw
  string : Spec.StringLaw
  seq : Spec.SeqLawful
  map : Spec.MapLawful
  refine : Spec.RefineLawful
  sigma : Spec.SigmaLawful
  sum : Spec.SumLawful
  delimited : Spec.DelimitedLawful
  lengthPrefixed : Spec.LengthPrefixedLawful
  many : Spec.ManyLawful
  manyTill : Spec.ManyTillLawful
  nat : Spec.NatLawful
  natBE : Spec.NatBELawful

def theVerifiedCodec : VerifiedCodec where
  law _ _ c _ _ hv hf := c.decode_encode hv hf
  encodeInjective _ _ c _ _ h0 ha hb h := c.encode_injective h0 ha hb h
  bytes _ c _ _ hv hf := c.decodeBytes_encodeBytes hv hf
  string _ c _ _ hv hf := c.decodeString_encodeString hv hf
  seq _ _ _ c d _ _ _ ha hb hx hr := Codec.seq_lawful c d ha hb hx hr
  map _ _ _ c f g h _ _ hb hr := Codec.map_lawful c f g h hb hr
  refine _ _ c P _ _ _ hx hr := Codec.refine_lawful c P hx hr
  sigma _ _ _ tag body _ _ _ ht hb hx hr := Codec.sigma_lawful tag body ht hb hx hr
  sum _ _ _ _ tl tr c d h _ hc hd :=
    ⟨fun _ ha => Codec.sum_lawful_inl tl tr c d h ha ⟨hc, hd⟩,
     fun _ hb => Codec.sum_lawful_inr tl tr c d h hb ⟨hc, hd⟩⟩
  delimited _ _ _ d c _ _ ha h0 hav := Codec.delimited_lawful d c ha h0 hav
  lengthPrefixed _ _ len c _ _ ha h0 hl hlf := Codec.lengthPrefixed_lawful len c ha h0 hl hlf
  many _ _ c _ h := Codec.many_lawful c h
  manyTill _ _ _ c term _ _ h := Codec.manyTill_lawful c term h
  nat n _ hr := Codec.nat_lawful n hr
  natBE w n r h := Codec.natBE_lawful w n r h

end Keel
