import Keel.RepoImpl.Codec

/-!
# Base codecs

* `Codec.nat`: a natural number in decimal, over characters. The decoder
  accepts leading zeros (`"007"` reads as `7`), as Python's `int` does; the
  encoder writes none. Only a non-digit may follow.
* `Codec.natBE w`: a natural number below `256 ^ w` as `w` big-endian bytes.
* `Codec.string`: the remaining characters, as a `String`.
* `Codec.bytes`: the remaining bytes, as a `ByteArray`.
-/

namespace Keel

open Parser

namespace Codec

/-! ## Decimal -/

/-- The character of a decimal digit. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- The value of a decimal digit character. -/
def digitValue (c : Char) : Nat := c.toNat - 48

/-- The shortest decimal digits of `n`. -/
def decimal (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else decimal (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by omega

/-- The value of a list of decimal digits, most significant first. -/
def digitsValue (l : List Char) : Nat := l.foldl (fun acc c => acc * 10 + digitValue c) 0

theorem isDigit_digitChar_fin : ∀ d : Fin 10, (digitChar d.val).isDigit = true := by decide

theorem digitValue_digitChar_fin : ∀ d : Fin 10, digitValue (digitChar d.val) = d.val := by decide

theorem isDigit_digitChar {d : Nat} (h : d < 10) : (digitChar d).isDigit = true :=
  isDigit_digitChar_fin ⟨d, h⟩

theorem digitValue_digitChar {d : Nat} (h : d < 10) : digitValue (digitChar d) = d :=
  digitValue_digitChar_fin ⟨d, h⟩

theorem decimal_isDigit (n : Nat) : ∀ c ∈ decimal n, c.isDigit = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decimal]
    split
    · simp [isDigit_digitChar (by omega : n < 10)]
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact ih _ (by omega) c hc
      · exact isDigit_digitChar (Nat.mod_lt _ (by omega))

theorem decimal_ne_nil (n : Nat) : decimal n ≠ [] := by
  rw [decimal]; split <;> simp

theorem digitsValue_append_digit (l : List Char) (c : Char) :
    digitsValue (l ++ [c]) = digitsValue l * 10 + digitValue c := by
  simp [digitsValue, List.foldl_append]

theorem digitsValue_decimal (n : Nat) : digitsValue (decimal n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decimal]
    split
    · simp [digitsValue, digitValue_digitChar (by omega : n < 10)]
    · rw [digitsValue_append_digit, ih _ (by omega), digitValue_digitChar (Nat.mod_lt _ (by omega))]
      omega

/-- No digit comes next. -/
def NoDigitNext (r : List Char) : Prop := ∀ c, r.head? = some c → c.isDigit = false

theorem takeWhile_isDigit_of_noDigitNext {r : List Char} (h : NoDigitNext r) :
    r.takeWhile Char.isDigit = [] := by
  cases r with
  | nil => rfl
  | cons c r => simp [h c rfl]

theorem dropWhile_isDigit_of_noDigitNext {r : List Char} (h : NoDigitNext r) :
    r.dropWhile Char.isDigit = r := by
  cases r with
  | nil => rfl
  | cons c r => simp [h c rfl]

theorem dropWhile_of_all {p : Char → Bool} : ∀ l : List Char, (∀ c ∈ l, p c = true) → l.dropWhile p = []
  | [], _ => rfl
  | c :: l, h => by
    simp only [List.dropWhile_cons, h c (by simp), ite_true]
    exact dropWhile_of_all l (fun x hx => h x (by simp [hx]))

/-- A natural number in decimal. -/
def nat : Codec Char Nat where
  encode := decimal
  parser := do
    let ds ← takeWhile Char.isDigit
    if ds.isEmpty then fail ParseError.unexpected else pure (digitsValue ds)
  valid _ := True
  follow := NoDigitNext
  parse_encode n r _ hf := by
    have hd := decimal_isDigit n
    have ht : (decimal n ++ r).takeWhile Char.isDigit = decimal n := by
      rw [List.takeWhile_append_of_pos hd, takeWhile_isDigit_of_noDigitNext hf, List.append_nil]
    have hdr : (decimal n ++ r).dropWhile Char.isDigit = r := by
      rw [List.dropWhile_append, dropWhile_of_all _ hd]; simp [dropWhile_isDigit_of_noDigitNext hf]
    simp [ht, hdr, decimal_ne_nil, digitsValue_decimal]

/-! ## Big-endian -/

/-- `n` as `w` big-endian bytes (only the low `8 * w` bits). -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => beBytes w (n / 256) ++ [(n % 256).toUInt8]

/-- The value of big-endian bytes. -/
def beValue (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem length_beBytes (w n : Nat) : (beBytes w n).length = w := by
  induction w generalizing n <;> simp_all [beBytes]

theorem beValue_beBytes (w n : Nat) (h : n < 256 ^ w) : beValue (beBytes w n) = n := by
  induction w generalizing n with
  | zero => simp at h; simp [beBytes, beValue, h]
  | succ w ih =>
    have h' : n / 256 < 256 ^ w := by rw [Nat.pow_succ] at h; omega
    have := ih (n / 256) h'
    simp only [beValue, beBytes, List.foldl_append, List.foldl_cons, List.foldl_nil] at this ⊢
    rw [this]
    simp only [Nat.toUInt8, UInt8.toNat_ofNat']
    omega

/-- A natural number below `256 ^ w` as `w` big-endian bytes. -/
def natBE (w : Nat) : Codec UInt8 Nat where
  encode := beBytes w
  parser := beValue <$> take w
  valid n := n < 256 ^ w
  follow _ := True
  parse_encode n r hv _ := by
    simp [parse_take w (beBytes w n) r (length_beBytes w n), beValue_beBytes w n hv]

/-! ## Raw text and bytes -/

/-- The remaining characters, as a string. -/
def string : Codec Char String :=
  rest.map String.ofList String.toList fun _ => String.ofList_toList

/-- The remaining bytes. -/
def bytes : Codec UInt8 ByteArray :=
  rest.map (fun l => ⟨l.toArray⟩) (fun b => b.data.toList) fun _ => by simp

end Codec

end Keel
