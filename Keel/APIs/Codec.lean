import Keel.Proofs.Codec
import Keel.APIs.Parse

/-!
# APIs: codecs on bytes and strings

* `Codec.encodeBytes` / `Codec.decodeBytes` for byte codecs, and
  `Codec.encodeString` / `Codec.decodeString` for character codecs, each with
  the round-trip law on any continuation.
* String literals as token lists: with `open Keel`, `"\r\n"` stands for its
  characters in a `Codec Char` and for its UTF-8 bytes in a `Codec UInt8`,
  so `Codec.delimited "\r\n" field |>.many` reads as it should.
* `Codable τ α`: a default codec for a type, with instances for `Nat`
  (decimal), `String`, `ByteArray`, `UInt8`, `Unit` and pairs.
-/

namespace Keel

/-! ## String literals as tokens -/

/-- Token types a string literal can be read as. -/
class Literal (τ : Type) where
  /-- The tokens of a string. -/
  ofString : String → List τ

instance : Literal Char := ⟨String.toList⟩
instance : Literal UInt8 := ⟨fun s => s.toList.flatMap String.utf8EncodeChar⟩

/-- With `open Keel`, a string literal coerces to its tokens. -/
scoped instance {τ : Type} [Literal τ] : Coe String (List τ) := ⟨Literal.ofString⟩

@[simp] theorem Literal.ofString_char (s : String) : (Literal.ofString s : List Char) = s.toList := rfl

namespace Codec

variable {α : Type}

/-! ## Bytes -/

/-- The encoding of `a`, as bytes. -/
def encodeBytes (c : Codec UInt8 α) (a : α) : ByteArray := ⟨(c.encode a).toArray⟩

/-- Decode from the start of a byte string: the value and the bytes left. Runs
on the `ByteArray` directly. -/
def decodeBytes (c : Codec UInt8 α) (b : ByteArray) : Option (α × ByteArray) :=
  match (c.parser (ε := Unit)).run b 0 with
  | .ok a j => some (a, b.extract j b.size)
  | .error _ _ => none

@[simp] theorem size_encodeBytes (c : Codec UInt8 α) (a : α) :
    (c.encodeBytes a).size = (c.encode a).length := by
  show (c.encode a).toArray.size = _; simp

/-- **The law on bytes**: decoding reads back the encoding from any
tolerated continuation, and leaves exactly the continuation. -/
theorem decodeBytes_encodeBytes (c : Codec UInt8 α) {a : α} {rest : ByteArray} (hv : c.valid a)
    (hf : c.follow rest.data.toList) : c.decodeBytes (c.encodeBytes a ++ rest) = some (a, rest) := by
  have hp := c.parse_encode (ε := Unit) a rest.data.toList hv hf
  have hl : Input.rest (c.encodeBytes a ++ rest) 0 = c.encode a ++ rest.data.toList := by
    simp [Input.rest, encodeBytes]
  rw [← hl] at hp
  have hrun := (c.parser (ε := Unit)).run_eq_of_parse hp (Nat.zero_le _)
  have hpos : Input.size (c.encodeBytes a ++ rest) - rest.data.toList.length = (c.encodeBytes a).size := by
    show (c.encodeBytes a ++ rest).size - _ = _
    rw [ByteArray.size_append]
    have : rest.data.toList.length = rest.size := by rw [Array.length_toList]; rfl
    omega
  rw [hpos] at hrun
  simp only [decodeBytes, hrun]
  rw [ByteArray.extract_append_eq_right rfl ByteArray.size_append]

/-! ## Strings -/

/-- The encoding of `a`, as a string. -/
def encodeString (c : Codec Char α) (a : α) : String := String.ofList (c.encode a)

/-- Decode from the start of a string: the value and the text left. Runs on
an array of the characters. -/
def decodeString (c : Codec Char α) (s : String) : Option (α × String) :=
  let cs := s.toList.toArray
  match (c.parser (ε := Unit)).run cs 0 with
  | .ok a j => some (a, String.ofList (cs.toList.drop j))
  | .error _ _ => none

/-- **The law on strings.** -/
theorem decodeString_encodeString (c : Codec Char α) {a : α} {rest : String} (hv : c.valid a)
    (hf : c.follow rest.toList) : c.decodeString (c.encodeString a ++ rest) = some (a, rest) := by
  have hp := c.parse_encode (ε := Unit) a rest.toList hv hf
  have hl : Input.rest (c.encodeString a ++ rest).toList.toArray 0 = c.encode a ++ rest.toList := by
    simp [Input.rest, Input.toList, encodeString]
  rw [← hl] at hp
  have hrun := (c.parser (ε := Unit)).run_eq_of_parse hp (Nat.zero_le _)
  simp only [decodeString, hrun]
  have hsz : Input.size (c.encodeString a ++ rest).toList.toArray - rest.toList.length =
      (c.encode a).length := by
    show (c.encodeString a ++ rest).toList.toArray.size - _ = _
    simp [encodeString]
  rw [hsz]
  simp [encodeString]

/-! ## Default codecs -/

end Codec

/-- A default codec for `α` over `τ` tokens. -/
class Codable (τ : Type) (α : Type) where
  codec : Codec τ α

/-- The default codec of `α`. -/
abbrev codecOf (τ : Type) (α : Type) [Codable τ α] : Codec τ α := Codable.codec

instance : Codable Char Nat := ⟨Codec.nat⟩
instance : Codable Char String := ⟨Codec.string⟩
instance : Codable UInt8 ByteArray := ⟨Codec.bytes⟩
instance : Codable UInt8 UInt8 := ⟨Codec.token⟩
instance {τ : Type} : Codable τ Unit := ⟨Codec.unit⟩
instance {τ α β : Type} [Codable τ α] [Codable τ β] : Codable τ (α × β) :=
  ⟨(codecOf τ α).seq (codecOf τ β)⟩

end Keel
