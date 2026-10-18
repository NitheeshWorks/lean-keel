import Keel.DataTypes.Parse

/-!
# The codec type

A `Codec τ α` is an encoder `α → List τ` and a decoder, which is a
`Keel.Parse` parser, together with the law that makes them a pair: the
decoder reads back what the encoder wrote, *on any continuation*,

  `decoder.parse (encode a ++ rest) = .ok a rest`.

The law is a field, so a `Codec` value is a proof. Two predicates make the law
honest without making it weak:

* `valid a`: the values the codec round-trips. Most codecs take every value;
  a delimited codec takes values whose encoding avoids the delimiter, a
  length-prefixed one values whose length its length field can hold. Each
  combinator states its `valid` in terms of its parts, so the condition is
  visible and `simp` discharges it for concrete codecs. `Codec.refine` moves it
  into the type.
* `follow rest`: the continuations the decoder tolerates. A prefix-free codec
  (a tag, a length-prefixed field, anything ending in a terminator) takes
  every continuation, `True`. A decimal number does not: `12` followed by `3`
  reads as `123`, so its `follow` says the next token is not a digit. This is
  the side condition that makes `_ext` lemmas compose.

The decoder is polymorphic in the error type: any `ε` with the library's
three error kinds. It runs on any buffer (`Keel.Input`), so the same codec
decodes a `List`, an `Array` or a `ByteArray`.
-/

namespace Keel

/-- A lawful codec of `α` values as `τ` tokens. -/
structure Codec (τ α : Type) where
  /-- The encoding of a value. -/
  encode : α → List τ
  /-- The decoder. -/
  parser : {ε : Type} → [ParseError ε] → Parser τ ε α
  /-- The values that round-trip. -/
  valid : α → Prop
  /-- The continuations the decoder tolerates after an encoding. -/
  follow : List τ → Prop
  /-- **The law**: the decoder reads back the encoding of a valid value from
  any tolerated continuation, leaving the continuation. -/
  parse_encode : ∀ {ε : Type} [ParseError ε] (a : α) (rest : List τ), valid a → follow rest →
    (parser (ε := ε)).parse (encode a ++ rest) = .ok a rest

/-- `l` and `m` are prefix-incomparable: neither is a prefix of the other. A
decoder that tests for `l` before reading something encoded as `m ++ …`
cannot mistake one for the other. Both lists are then non-empty. -/
def Incomparable {τ : Type} (l m : List τ) : Prop := ¬ l <+: m ∧ ¬ m <+: l

/-- The first occurrence of `d` in `l ++ d` is at the end of `l`: no
occurrence starts inside `l`. This is the escaping side condition of a
delimited field. -/
def Avoids {τ : Type} (d l : List τ) : Prop := ∀ k, k < l.length → ¬ d <+: (l ++ d).drop k

instance {τ : Type} [DecidableEq τ] (l m : List τ) : Decidable (Incomparable l m) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance {τ : Type} [DecidableEq τ] (d l : List τ) : Decidable (Avoids d l) :=
  inferInstanceAs (Decidable (∀ k, k < l.length → _))

end Keel
