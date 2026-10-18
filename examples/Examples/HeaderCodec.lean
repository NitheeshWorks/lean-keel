import Keel

/-!
# Example: a codec built from combinators

A header block, as a binary framing might carry it: every header is a name,
`": "`, and a value, framed by a two-byte big-endian length, and the block
ends with an empty frame `00 00`.

The codec is assembled from Keel's combinators, and the conditions under
which it round-trips live in the types of the header fields: a name has no
`:`, and name and value are short enough for their frame. So the round trip
holds for *every* header list, on any continuation (`roundTrip`), proved
from the combinators' laws with no reasoning about bytes.

Inherits: `Codec.decode_encode`, through `manyTill_lawful`,
`lengthPrefixed_lawful`, `delimited_lawful` and `seq_lawful`.
-/

namespace Examples.HeaderCodec

open Keel

/-- A header name: at most 1000 bytes, none of them `:` (58). -/
abbrev Name := {n : List UInt8 // 58 ∉ n ∧ n.length ≤ 1000}

/-- A header value: at most 1000 bytes. -/
abbrev Value := {v : List UInt8 // v.length ≤ 1000}

/-- `name: value`. -/
def header : Codec UInt8 (Name × Value) :=
  (Codec.delimited [58, 32] ((Codec.rest).refine fun n => 58 ∉ n ∧ n.length ≤ 1000)).seq
    ((Codec.rest).refine fun v => v.length ≤ 1000)

/-- A header in a two-byte length frame. -/
def frame : Codec UInt8 (Name × Value) := Codec.lengthPrefixed (Codec.natBE 2) header

/-- The block: frames until an empty one. -/
def headers : Codec UInt8 (List (Name × Value)) := frame.manyTill [0, 0]

/-! ## Why every header list round-trips -/

theorem header_encode (n : Name) (v : Value) : header.encode (n, v) = n.1 ++ [58, 32] ++ v.1 := rfl

theorem header_valid (h : Name × Value) : header.valid h := by
  obtain ⟨⟨n, hn, _⟩, ⟨v, _⟩⟩ := h
  simp [header, Codec.avoids_cons_of_not_mem hn]

theorem frame_valid (h : Name × Value) : frame.valid h := by
  obtain ⟨⟨n, hn, hnl⟩, ⟨v, hv⟩⟩ := h
  refine (Codec.lengthPrefixed_valid _ _ _).2 ⟨header_valid _, by simp [header], ?_, by simp⟩
  simp only [header_encode, Codec.natBE_valid, List.length_append, List.length_cons, List.length_nil]
  omega

/-- A frame never starts like the terminator: its length field is at least 2. -/
theorem frame_incomparable (h : Name × Value) : Incomparable [0, 0] (frame.encode h) := by
  obtain ⟨⟨n, hn, hnl⟩, ⟨v, hv⟩⟩ := h
  simp only [frame, Codec.lengthPrefixed_encode, header_encode, Codec.natBE_encode]
  have hlen : 2 ≤ (n ++ [58, 32] ++ v).length ∧ (n ++ [58, 32] ++ v).length < 65536 := by
    simp; omega
  generalize (n ++ [58, 32] ++ v) = e at hlen ⊢
  simp only [Codec.beBytes, List.nil_append, List.singleton_append]
  constructor
  · intro hp
    have h1 := congrArg UInt8.toNat (List.cons_prefix_cons.1 hp).1
    have h2 := congrArg UInt8.toNat (List.cons_prefix_cons.1 (List.cons_prefix_cons.1 hp).2).1
    have hA : e.length / 256 % 256 % 256 = 0 := by simpa [Nat.toUInt8, UInt8.toNat_ofNat'] using h1.symm
    have hB : e.length % 256 = 0 := by simpa [Nat.toUInt8, UInt8.toNat_ofNat'] using h2.symm
    omega
  · intro hp
    have := hp.length_le
    simp only [List.length_cons, List.length_append, List.length_nil] at this
    omega

/-- **Every header list round-trips, on any continuation.** -/
theorem roundTrip (hs : List (Name × Value)) (rest : List UInt8) :
    headers.decode (headers.encode hs ++ rest) = some (hs, rest) := by
  apply Codec.manyTill_lawful
  induction hs with
  | nil => trivial
  | cons h hs ih => exact ⟨frame_valid h, frame_incomparable h, fun _ => trivial, ih⟩

/-! ## Running it -/

def name! (s : String) : Name :=
  let b := s.toUTF8.data.toList
  if h : 58 ∉ b ∧ b.length ≤ 1000 then ⟨b, h⟩ else ⟨[], by simp⟩

def value! (s : String) : Value :=
  let b := s.toUTF8.data.toList
  if h : b.length ≤ 1000 then ⟨b, h⟩ else ⟨[], by simp⟩

def sample : List (Name × Value) :=
  [(name! "host", value! "example.org"), (name! "accept", value! "*/*")]

def run : IO Unit := do
  let wire := headers.encodeBytes sample
  IO.println s!"header block: {wire.size} bytes"
  match headers.decodeBytes (wire ++ "tail".toUTF8) with
  | some (hs, rest) =>
    for (n, v) in hs do
      IO.println s!"  {String.fromUTF8! ⟨n.1.toArray⟩}: {String.fromUTF8! ⟨v.1.toArray⟩}"
    IO.println s!"  left over: {String.fromUTF8! rest}"
  | none => IO.println "  decode failed"

end Examples.HeaderCodec
