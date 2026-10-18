import Keel.Proofs.Parse
import Keel.Specifications.Parse
import Keel.Specifications.Codec
import Keel.Specifications.Refine
import Keel.Specifications.Route

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
  fixDepthZero : Spec.ParseFixDepthZero
  fixDepthSucc : Spec.ParseFixDepthSucc
  fixDepthEqFix : Spec.FixDepthEqFix

theorem theVerifiedParse : VerifiedParse where
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
  fixDepthZero _ _ _ _ := Parser.parse_fixDepth_zero
  fixDepthSucc _ _ _ _ := Parser.parse_fixDepth_succ
  fixDepthEqFix _ _ _ _ F d l h := Parser.fixDepth_eq_fix F d l h

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

theorem theVerifiedCodec : VerifiedCodec where
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

/-- Refinement and validation: soundness and completeness, and the
location laws of validators. -/
structure VerifiedRefine where
  validateIff : Spec.ValidateIff
  errorsNonempty : Spec.ValidateErrorsNonempty
  validateAnd : Spec.ValidateAnd
  refineIff : Spec.RefineIff
  atPathAppend : Spec.AtPathAppend
  locAtPath : Spec.LocAtPath
  bothOkIff : Spec.BothOkIff
  eachOkIff : Spec.EachOkIff
  locEach : Spec.LocEach
  pickFind : Spec.PickFind

theorem theVerifiedRefine : VerifiedRefine where
  validateIff _ c x := Constraint.validate_iff c x
  errorsNonempty _ c _ _ h := Constraint.validate_error_ne_nil c h
  validateAnd _ c d x := Constraint.validate_and_iff c d x
  refineIff _ c x := Constraint.refine_ok_iff c x
  atPathAppend _ _ _ _ p q v := Validator.atPath_append p q v
  locAtPath _ _ _ _ p v x es h := Validator.prefix_loc_atPath p v x es h
  bothOkIff _ _ _ _ v w x a b := Validator.both_ok_iff v w x a b
  eachOkIff _ _ _ _ v xs ys := Validator.each_ok_iff v xs ys
  locEach _ _ _ _ v xs es h := Validator.loc_each v xs es h
  pickFind _ _ norm cs x v := Constraint.pick_ok_iff norm cs x v

/-- Routing: templates round-trip, and dispatch is first match with the
405 and 404 conditions characterised. -/
structure VerifiedRoute where
  matchUrlFor : Spec.MatchUrlFor
  urlForMatch : Spec.UrlForMatch
  firstMatch : Spec.DispatchFirstMatch
  dispatchPartial : Spec.DispatchPartial
  dispatchNone : Spec.DispatchNone
  resolveFirstMatch : Spec.ResolveFirstMatch
  methodNotAllowed : Spec.MethodNotAllowedIff
  allowFirstPartial : Spec.AllowFirstPartial
  allowUnionOfPartials : Spec.AllowUnionOfPartials
  notFound : Spec.NotFoundIff

theorem theVerifiedRoute : VerifiedRoute where
  matchUrlFor t v ha hv := t.match_urlFor ha v hv
  urlForMatch t _ _ h hc := t.urlFor_match h hc
  firstMatch _ _ m rs r b := dispatch_found_iff m rs r b
  dispatchPartial _ _ m rs := dispatch_partial_iff m rs
  dispatchNone _ _ m rs := dispatch_none_iff m rs
  resolveFirstMatch _ rs method path r v policy := Router.resolve_found_iff rs method path r v policy
  methodNotAllowed _ rs method path policy := Router.methodNotAllowed_iff rs method path policy
  allowFirstPartial _ rs method path r allow h := Router.methodNotAllowed_allow_first rs method path r allow h
  allowUnionOfPartials _ rs method path r allow h :=
    Router.methodNotAllowed_allow_union rs method path r allow h
  notFound _ rs method path policy := Router.notFound_iff rs method path policy

end Keel
