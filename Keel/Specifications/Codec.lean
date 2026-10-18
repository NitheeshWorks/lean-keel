import Keel.APIs.Codec

/-!
# Specifications: lawful codecs

The headline laws of `Keel.Codec`. Each is proved in `Proofs/Codec.lean` (or,
for the byte and string forms, `APIs/Codec.lean`) and has a slot in
`Proofs/Verified.lean`.
-/

namespace Keel.Spec

open Codec

/-- Every codec reads back what it wrote, on any tolerated continuation. -/
def CodecLaw : Prop :=
  ∀ (τ α : Type) (c : Codec τ α) (a : α) (r : List τ), c.valid a → c.follow r →
    c.decode (c.encode a ++ r) = some (a, r)

/-- Encoding is injective on valid values. -/
def EncodeInjective : Prop :=
  ∀ (τ α : Type) (c : Codec τ α) (a b : α), c.follow [] → c.valid a → c.valid b →
    c.encode a = c.encode b → a = b

/-- The law on byte strings, run on the `ByteArray` itself. -/
def BytesLaw : Prop :=
  ∀ (α : Type) (c : Codec UInt8 α) (a : α) (rest : ByteArray), c.valid a → c.follow rest.data.toList →
    c.decodeBytes (c.encodeBytes a ++ rest) = some (a, rest)

/-- The law on strings. -/
def StringLaw : Prop :=
  ∀ (α : Type) (c : Codec Char α) (a : α) (rest : String), c.valid a → c.follow rest.toList →
    c.decodeString (c.encodeString a ++ rest) = some (a, rest)

/-- Sequencing is lawful. -/
def SeqLawful : Prop :=
  ∀ (τ α β : Type) (c : Codec τ α) (d : Codec τ β) (a : α) (b : β) (r : List τ),
    c.valid a → d.valid b → (∀ r, d.follow r → c.follow (d.encode b ++ r)) → d.follow r →
      (c.seq d).decode (c.encode a ++ d.encode b ++ r) = some ((a, b), r)

/-- Mapping along a left inverse is lawful. -/
def MapLawful : Prop :=
  ∀ (τ α β : Type) (c : Codec τ α) (f : α → β) (g : β → α) (h : Function.LeftInverse f g)
    (b : β) (r : List τ), c.valid (g b) → c.follow r →
      (c.map f g h).decode (c.encode (g b) ++ r) = some (b, r)

/-- Refining to a subtype is lawful. -/
def RefineLawful : Prop :=
  ∀ (τ α : Type) (c : Codec τ α) (P : α → Prop) [DecidablePred P] (x : {a // P a}) (r : List τ),
    c.valid x.1 → c.follow r → (c.refine P).decode (c.encode x.1 ++ r) = some (x, r)

/-- Choice by a decoded tag is lawful. -/
def SigmaLawful : Prop :=
  ∀ (τ T : Type) (β : T → Type) (tag : Codec τ T) (body : (t : T) → Codec τ (β t)) (t : T) (b : β t)
    (r : List τ), tag.valid t → (body t).valid b →
      (∀ r, (body t).follow r → tag.follow ((body t).encode b ++ r)) → (∀ t, (body t).follow r) →
        (sigma tag body).decode (tag.encode t ++ (body t).encode b ++ r) = some (⟨t, b⟩, r)

/-- Choice by incomparable literal tags is lawful, on both sides. -/
def SumLawful : Prop :=
  ∀ (τ α β : Type) [DecidableEq τ] (tl tr : List τ) (c : Codec τ α) (d : Codec τ β)
    (h : Incomparable tl tr) (r : List τ), c.follow r → d.follow r →
      (∀ a, c.valid a → (sum tl tr c d h).decode (tl ++ c.encode a ++ r) = some (.inl a, r)) ∧
      (∀ b, d.valid b → (sum tl tr c d h).decode (tr ++ d.encode b ++ r) = some (.inr b, r))

/-- A delimited field is lawful on any continuation when its encoding avoids
the delimiter. -/
def DelimitedLawful : Prop :=
  ∀ (τ α : Type) [DecidableEq τ] (d : List τ) (c : Codec τ α) (a : α) (r : List τ),
    c.valid a → c.follow [] → Avoids d (c.encode a) →
      (delimited d c).decode (c.encode a ++ d ++ r) = some (a, r)

/-- A length-prefixed field is lawful on any continuation. -/
def LengthPrefixedLawful : Prop :=
  ∀ (τ α : Type) (len : Codec τ Nat) (c : Codec τ α) (a : α) (r : List τ),
    c.valid a → c.follow [] → len.valid (c.encode a).length → (∀ r, len.follow (c.encode a ++ r)) →
      (lengthPrefixed len c).decode (len.encode (c.encode a).length ++ c.encode a ++ r) = some (a, r)

/-- Repetition to the end of input is lawful. -/
def ManyLawful : Prop :=
  ∀ (τ α : Type) (c : Codec τ α) (xs : List α), ManyValid c xs →
    c.many.decode (xs.flatMap c.encode) = some (xs, [])

/-- Repetition up to a terminator is lawful on any continuation. -/
def ManyTillLawful : Prop :=
  ∀ (τ α : Type) [DecidableEq τ] (c : Codec τ α) (term : List τ) (xs : List α) (r : List τ),
    ManyTillValid c term xs → (c.manyTill term).decode (xs.flatMap c.encode ++ term ++ r) = some (xs, r)

/-- Decimal numbers round-trip before any non-digit. -/
def NatLawful : Prop :=
  ∀ (n : Nat) (r : List Char), NoDigitNext r → nat.decode (decimal n ++ r) = some (n, r)

/-- Fixed-width big-endian numbers round-trip when they fit. -/
def NatBELawful : Prop :=
  ∀ (w n : Nat) (r : List UInt8), n < 256 ^ w → (natBE w).decode (beBytes w n ++ r) = some (n, r)

/-- Compiled code renders decimals by `decimalFast`: equal to `decimal`. -/
def DecimalFast : Prop := Codec.decimal = Codec.decimalFast

/-- Compiled code reads digits by `digitsValueFast`: equal to `digitsValue`. -/
def DigitsValueFast : Prop := Codec.digitsValue = Codec.digitsValueFast

end Keel.Spec
