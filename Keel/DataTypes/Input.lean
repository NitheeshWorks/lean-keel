/-!
# Inputs: what a parser reads

A parser reads tokens by position from a buffer. `Input σ τ` says that `σ` is
a buffer of `τ` tokens with constant-time access, and relates it to its list
of tokens, `Input.toList`. Every law in `Keel.Parse` and `Keel.Codec` is
stated on lists; the laws carry over to any buffer through this relation, so
the same parser runs on a `ByteArray` and is reasoned about on a `List UInt8`.

Instances: `List τ` (the reference, used in statements), `Array τ`,
`ByteArray`, and `Slice σ`, a buffer cut short at a stop position, which is
how a decoder confines an inner decoder to a delimited or length-prefixed
region without copying.
-/

namespace Keel

/-- `σ` is a buffer of `τ` tokens. `toList` is its meaning; `size` and `get?`
are the fast accessors, and the two laws tie them to `toList`. -/
class Input (σ : Type) (τ : outParam Type) where
  /-- The tokens of the buffer, in order. -/
  toList : σ → List τ
  /-- The number of tokens. -/
  size : σ → Nat
  /-- The token at a position, if there is one. -/
  get? : σ → Nat → Option τ
  size_eq : ∀ s, size s = (toList s).length
  get?_eq : ∀ s i, get? s i = (toList s)[i]?

namespace Input

variable {σ τ : Type} [Input σ τ]

/-- The tokens from position `i` on. -/
abbrev rest (s : σ) (i : Nat) : List τ := (toList s).drop i

theorem length_rest (s : σ) (i : Nat) : (rest s i).length = size s - i := by
  simp [rest, size_eq]

theorem get?_rest (s : σ) (i k : Nat) : (rest s i)[k]? = get? s (i + k) := by
  simp [rest, get?_eq]

end Input

instance {τ : Type} : Input (List τ) τ where
  toList := id
  size := List.length
  get? l i := l[i]?
  size_eq _ := rfl
  get?_eq _ _ := rfl

@[simp] theorem Input.toList_list {τ : Type} (l : List τ) : Input.toList l = l := rfl
@[simp] theorem Input.size_list {τ : Type} (l : List τ) : Input.size l = l.length := rfl
@[simp] theorem Input.get?_list {τ : Type} (l : List τ) (i : Nat) : Input.get? l i = l[i]? := rfl

instance {τ : Type} : Input (Array τ) τ where
  toList := Array.toList
  size := Array.size
  get? a i := a[i]?
  size_eq _ := rfl
  get?_eq a i := by simp

instance : Input ByteArray UInt8 where
  toList b := b.data.toList
  size := ByteArray.size
  get? b i := b[i]?
  size_eq _ := rfl
  get?_eq b i := by
    by_cases h : i < b.size
    · rw [getElem?_pos b i h, List.getElem?_eq_getElem (by simpa using h)]
      simp [ByteArray.getElem_eq_getElem_data]
    · rw [getElem?_neg b i h, List.getElem?_eq_none (by simp; simpa using h)]

@[simp] theorem Input.toList_byteArray (b : ByteArray) : Input.toList b = b.data.toList := rfl

/-- A buffer read only up to position `stop`: positions at or past `stop`
hold nothing. Positions are those of the underlying buffer, so a parser run
on a slice reports positions that are valid in the whole buffer. -/
structure Slice (σ : Type) where
  buf : σ
  stop : Nat

instance {σ τ : Type} [Input σ τ] : Input (Slice σ) τ where
  toList s := (Input.toList s.buf).take s.stop
  size s := min s.stop (Input.size s.buf)
  get? s i := if i < s.stop then Input.get? s.buf i else none
  size_eq s := by simp [Input.size_eq]
  get?_eq s i := by
    by_cases h : i < s.stop
    · simp [h, Input.get?_eq]
    · simp [h, List.getElem?_take]

@[simp] theorem Input.toList_slice {σ τ : Type} [Input σ τ] (s : Slice σ) :
    Input.toList s = (Input.toList s.buf).take s.stop := rfl

end Keel
