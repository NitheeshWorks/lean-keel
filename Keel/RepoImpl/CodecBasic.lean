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

/-! ## Long decimals in compiled code

`decimal` and `digitsValue` are the specifications. Compiled code runs
`decimalFast` (an accumulator, eighteen digits per division: no append, no
recursion depth) and
`digitsValueFast` (digit runs joined pairwise, so each big-number product is
between halves of similar size), through `@[csimp]` on their equalities. -/

/-- `decimal n ++ acc`, by an accumulator. -/
def decimalAcc (n : Nat) (acc : List Char) : List Char :=
  if n < 10 then digitChar n :: acc else decimalAcc (n / 10) (digitChar (n % 10) :: acc)
termination_by n
decreasing_by omega

theorem decimalAcc_eq (n : Nat) : ∀ acc, decimalAcc n acc = decimal n ++ acc := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro acc
    rw [decimalAcc, decimal]
    split
    · rfl
    · rw [ih _ (by omega)]; simp

/-- The last `k` digits of `m`, leading zeros included, in front of `acc`. -/
def padAcc : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | k + 1, m, acc => padAcc k (m / 10) (digitChar (m % 10) :: acc)

theorem decimalAcc_split : ∀ (k n : Nat) (acc : List Char), 10 ^ k ≤ n →
    decimalAcc n acc = decimalAcc (n / 10 ^ k) (padAcc k (n % 10 ^ k) acc)
  | 0, n, acc, _ => by simp [padAcc]
  | k + 1, n, acc, h => by
    have h10 : ¬ n < 10 := by
      have : 10 ≤ 10 ^ (k + 1) := by
        rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left 10 (Nat.pow_pos (by decide))
      omega
    have hk : 10 ^ k ≤ n / 10 := by
      rw [Nat.le_div_iff_mul_le (by decide), ← Nat.pow_succ]; exact h
    rw [decimalAcc, ite_eq_right h10, decimalAcc_split k (n / 10) _ hk, padAcc, Nat.pow_succ',
      Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod, Nat.div_div_eq_div_mul]

/-- `decimal n ++ acc`, eighteen digits per big-number division. -/
def decimalChunks (n : Nat) (acc : List Char) : List Char :=
  if n < 10 ^ 18 then decimalAcc n acc
  else decimalChunks (n / 10 ^ 18) (padAcc 18 (n % 10 ^ 18) acc)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem decimalChunks_eq (n : Nat) : ∀ acc, decimalChunks n acc = decimalAcc n acc := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro acc
    rw [decimalChunks]
    split
    · rfl
    · rename_i h
      rw [ih _ (Nat.div_lt_self (by omega) (by decide)), ← decimalAcc_split 18 n acc (by omega)]

/-- `decimal`, by an accumulator, eighteen digits at a time. -/
def decimalFast (n : Nat) : List Char := decimalChunks n []

@[csimp] theorem decimal_csimp : @decimal = @decimalFast :=
  funext fun n => by simp [decimalFast, decimalChunks_eq, decimalAcc_eq]

/-- The value of digit runs `(value, length)`, most significant first. -/
def runsValue (l : List (Nat × Nat)) : Nat := l.foldl (fun acc x => acc * 10 ^ x.2 + x.1) 0

/-- Join adjacent digit runs pairwise, in one tail-recursive pass (`acc`
holds the joined runs, reversed). -/
def joinPairs : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | acc, (a, la) :: (b, lb) :: rest => joinPairs ((a * 10 ^ lb + b, la + lb) :: acc) rest
  | acc, [x] => (x :: acc).reverse
  | acc, [] => acc.reverse

theorem joinPairs_length : ∀ (acc l : List (Nat × Nat)),
    (joinPairs acc l).length = acc.length + (l.length + 1) / 2
  | acc, (a, la) :: (b, lb) :: rest => by
    rw [joinPairs, joinPairs_length]; simp; omega
  | acc, [x] => by simp [joinPairs]
  | acc, [] => by simp [joinPairs]

theorem joinPairs_value : ∀ (z : Nat) (acc l : List (Nat × Nat)),
    (joinPairs acc l).foldl (fun acc x => acc * 10 ^ x.2 + x.1) z =
      l.foldl (fun acc x => acc * 10 ^ x.2 + x.1) (acc.reverse.foldl (fun acc x => acc * 10 ^ x.2 + x.1) z)
  | z, acc, (a, la) :: (b, lb) :: rest => by
    rw [joinPairs, joinPairs_value]
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    congr 1
    rw [Nat.pow_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  | z, acc, [x] => by simp [joinPairs, List.foldl_append]
  | z, acc, [] => by simp [joinPairs]

/-- The value of digit runs, joining pairs until one run is left: about
`log₂ n` passes. -/
def joinAll (l : List (Nat × Nat)) : Nat :=
  match l with
  | [] => 0
  | [x] => x.1
  | x :: y :: rest => joinAll (joinPairs [] (x :: y :: rest))
termination_by l.length
decreasing_by rw [joinPairs_length]; simp; omega

theorem joinAll_eq (l : List (Nat × Nat)) : joinAll l = runsValue l := by
  induction l using joinAll.induct with
  | case1 => simp [joinAll, runsValue]
  | case2 x => simp [joinAll, runsValue]
  | case3 x y rest ih =>
    rw [joinAll, ih, runsValue, runsValue, joinPairs_value]; rfl

/-- `digitsValue`, joining digit runs pairwise. -/
def digitsValueFast (l : List Char) : Nat := joinAll (l.map fun c => (digitValue c, 1))

@[csimp] theorem digitsValue_csimp : @digitsValue = @digitsValueFast := by
  funext l
  simp only [digitsValueFast, joinAll_eq, runsValue, List.foldl_map, Nat.pow_one, digitsValue]

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
