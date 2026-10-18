import Keel.RepoImpl.Route
import Keel.RepoImpl.CodecBasic

/-!
# Starlette's convertors, lawful

| name | starlette regex | value | rendering |
|---|---|---|---|
| `str` | `[^/]+` | `String` | itself; must be non-empty without `/` |
| `path` | `.*` | `String` | itself |
| `int` | `[0-9]+` | `Nat` | decimal, no leading zeros |
| `float` | `[0-9]+(\.[0-9]+)?` | `Fixed` (exact decimal) | digits, trailing zeros dropped |
| `uuid` | 8-4-4-4-12 hex, hyphens optional | `UUID` | lower case, hyphenated |

`float` values are exact decimals rather than IEEE doubles: starlette renders
a float with `"%0.20f"` and strips zeros, so `0.1` renders as
`0.10000000000000000555`; here `0.1` renders as `0.1`. lean-starlette records
the difference as a deviation.
-/

namespace Keel

namespace Convertor

/-! ## str and path -/

/-- `str`: one non-empty path segment. -/
@[reducible] def str : Convertor where
  name := "str"
  Val := String
  accepts t := !t.isEmpty && !t.contains '/'
  parse t := some (String.ofList t)
  render s := s.toList
  Valid s := s.toList ≠ [] ∧ '/' ∉ s.toList
  accepts_render s h := by simp [h.1, h.2]
  parse_render s _ := by simp
  segment := true
  segment_spec _ t h := (by simpa using h : t ≠ [] ∧ '/' ∉ t).2

/-- `path`: any text, `/` included. -/
@[reducible] def path : Convertor where
  name := "path"
  Val := String
  accepts _ := true
  parse t := some (String.ofList t)
  render s := s.toList
  Valid _ := True
  accepts_render _ _ := rfl
  parse_render s _ := by simp
  segment := false
  segment_spec h := by cases h

/-! ## int -/

/-- `int`: decimal digits, as a natural number. Leading zeros are accepted
(`007` is `7`) and never rendered. -/
@[reducible] def int : Convertor where
  name := "int"
  Val := Nat
  accepts t := !t.isEmpty && t.all Char.isDigit
  parse t := some (Codec.digitsValue t)
  render := Codec.decimal
  Valid _ := True
  accepts_render n _ := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
    exact ⟨Codec.decimal_ne_nil n, Codec.decimal_isDigit n⟩
  parse_render n _ := by simp [Codec.digitsValue_decimal]
  segment := true
  segment_spec _ t h hs := by
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact absurd (h.2 '/' hs) (by decide)

/-! ## float -/

/-- An exact non-negative decimal: whole part and fractional digits, with no
trailing zero in the fraction. -/
structure Fixed where
  whole : Nat
  frac : List Char
  deriving DecidableEq, Repr

/-- Drop trailing zeros. -/
def stripZeros (l : List Char) : List Char := (l.reverse.dropWhile (· == '0')).reverse

/-- The shape `[0-9]+(\.[0-9]+)?`. -/
def floatShape (t : List Char) : Bool :=
  let w := t.takeWhile Char.isDigit
  let r := t.dropWhile Char.isDigit
  !w.isEmpty && (r.isEmpty || (r.head? == some '.' && !r.tail.isEmpty && r.tail.all Char.isDigit))

theorem stripZeros_of_last {l : List Char} (h : l.getLast? ≠ some '0') : stripZeros l = l := by
  unfold stripZeros
  cases hl : l.reverse with
  | nil => simp_all
  | cons x xs =>
    have : x ≠ '0' := by
      intro hx; apply h
      rw [← List.head?_reverse, hl, hx]; rfl
    rw [List.dropWhile_cons, ite_eq_right (by simpa using this), ← hl, List.reverse_reverse]

theorem mem_takeWhile {p : Char → Bool} : ∀ {l : List Char} {c : Char}, c ∈ l.takeWhile p → p c = true
  | [], _, h => by simp at h
  | x :: l, c, h => by
    by_cases hx : p x
    · simp only [List.takeWhile_cons, hx, ite_true, List.mem_cons] at h
      rcases h with rfl | h
      · exact hx
      · exact mem_takeWhile h
    · simp [hx] at h

theorem takeWhile_digits_append {w r : List Char} (hw : ∀ c ∈ w, c.isDigit = true)
    (hr : ∀ c, r.head? = some c → c.isDigit = false) : (w ++ r).takeWhile Char.isDigit = w := by
  rw [List.takeWhile_append_of_pos hw]
  cases r with
  | nil => simp
  | cons c r => simp [hr c rfl]

theorem dropWhile_digits_append {w r : List Char} (hw : ∀ c ∈ w, c.isDigit = true)
    (hr : ∀ c, r.head? = some c → c.isDigit = false) : (w ++ r).dropWhile Char.isDigit = r := by
  rw [List.dropWhile_append, Codec.dropWhile_of_all _ hw]
  cases r with
  | nil => simp
  | cons c r => simp [hr c rfl]

/-- The rendering of a `Fixed`. -/
def renderFixed (f : Fixed) : List Char :=
  Codec.decimal f.whole ++ (if f.frac = [] then [] else '.' :: f.frac)

/-- `float`: `[0-9]+(\.[0-9]+)?`, as an exact decimal. -/
@[reducible] def float : Convertor where
  name := "float"
  Val := Fixed
  accepts := floatShape
  parse t :=
    let w := t.takeWhile Char.isDigit
    let r := t.dropWhile Char.isDigit
    some ⟨Codec.digitsValue w, stripZeros (r.drop 1)⟩
  render := renderFixed
  Valid f := (∀ c ∈ f.frac, c.isDigit = true) ∧ f.frac.getLast? ≠ some '0'
  accepts_render f h := by
    have hd := Codec.decimal_isDigit f.whole
    have hne := Codec.decimal_ne_nil f.whole
    have hstop : ∀ c, (if f.frac = [] then [] else '.' :: f.frac).head? = some c → c.isDigit = false := by
      intro c hc; split at hc
      · simp at hc
      · simp at hc; subst hc; decide
    simp only [floatShape, renderFixed, takeWhile_digits_append hd hstop,
      dropWhile_digits_append hd hstop]
    by_cases hf : f.frac = []
    · simp [hf, hne]
    · simp [hf, hne, List.all_eq_true.2 h.1]
  parse_render f h := by
    have hd := Codec.decimal_isDigit f.whole
    have hstop : ∀ c, (if f.frac = [] then [] else '.' :: f.frac).head? = some c → c.isDigit = false := by
      intro c hc; split at hc
      · simp at hc
      · simp at hc; subst hc; decide
    simp only [renderFixed, takeWhile_digits_append hd hstop, dropWhile_digits_append hd hstop,
      Codec.digitsValue_decimal]
    cases f with
    | mk w fr =>
      by_cases hf : fr = []
      · subst hf; simp [stripZeros]
      · simp [hf, stripZeros_of_last h.2]
  segment := true
  segment_spec _ t h hs := by
    simp only [floatShape, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨_, hr⟩ := h
    have hsplit := List.takeWhile_append_dropWhile (p := Char.isDigit) (l := t)
    rw [← hsplit] at hs
    rcases List.mem_append.1 hs with hs | hs
    · exact absurd (mem_takeWhile hs) (by decide)
    · rcases hr with hr | ⟨⟨hh, _⟩, hall⟩
      · simp [List.isEmpty_iff.1 hr] at hs
      · cases hrest : t.dropWhile Char.isDigit with
        | nil => simp [hrest] at hh
        | cons x xs =>
          rw [hrest] at hs hh hall
          simp at hh hall
          rcases List.mem_cons.1 hs with hs | hs
          · exact absurd (hs.trans hh) (by decide)
          · exact absurd (hall '/' hs) (by decide)

/-! ## uuid -/

/-- A hexadecimal digit, either case. -/
def isHex (c : Char) : Bool :=
  decide (48 ≤ c.toNat ∧ c.toNat ≤ 57) || decide (97 ≤ c.toNat ∧ c.toNat ≤ 102) ||
    decide (65 ≤ c.toNat ∧ c.toNat ≤ 70)

/-- A lower-case hexadecimal digit. -/
def isLowerHex (c : Char) : Bool :=
  decide (48 ≤ c.toNat ∧ c.toNat ≤ 57) || decide (97 ≤ c.toNat ∧ c.toNat ≤ 102)

/-- Lower-case a hex digit (other characters are unchanged). -/
def lowerHex (c : Char) : Char :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then Char.ofNat (c.toNat + 32) else c

theorem isHex_of_lower {c : Char} (h : isLowerHex c = true) : isHex c = true := by
  simp only [isLowerHex, isHex, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega

theorem ne_hyphen_of_isHex {c : Char} (h : isHex c = true) : c ≠ '-' := by
  rintro rfl; simp [isHex] at h

theorem ne_slash_of_isHex {c : Char} (h : isHex c = true) : c ≠ '/' := by
  rintro rfl; simp [isHex] at h

theorem lowerHex_of_lower {c : Char} (h : isLowerHex c = true) : lowerHex c = c := by
  simp only [isLowerHex, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [lowerHex]
  rw [ite_eq_right (by omega)]

/-- A UUID: its five groups of lower-case hex digits, of lengths 8, 4, 4, 4
and 12. -/
structure UUID where
  g1 : List Char
  g2 : List Char
  g3 : List Char
  g4 : List Char
  g5 : List Char
  len : g1.length = 8 ∧ g2.length = 4 ∧ g3.length = 4 ∧ g4.length = 4 ∧ g5.length = 12
  hex : ∀ c ∈ g1 ++ g2 ++ g3 ++ g4 ++ g5, isLowerHex c = true

/-- The 32 digits of a UUID. -/
def UUID.digits (u : UUID) : List Char := u.g1 ++ u.g2 ++ u.g3 ++ u.g4 ++ u.g5

/-- Hex groups of the given lengths, each optionally followed by a hyphen
before the next. -/
def hexGroups : List Nat → List Char → Bool
  | [], t => t.isEmpty
  | n :: ns, t =>
    (t.take n).length == n && (t.take n).all isHex &&
      match t.drop n with
      | '-' :: r => !ns.isEmpty && hexGroups ns r
      | r => hexGroups ns r

/-- The UUID shape: `8-4-4-4-12` hex digits, hyphens optional. -/
def uuidShape (t : List Char) : Bool := hexGroups [8, 4, 4, 4, 12] t

/-- The canonical text of a UUID: lower case, hyphenated. -/
def renderUUID (u : UUID) : List Char :=
  u.g1 ++ '-' :: u.g2 ++ '-' :: u.g3 ++ '-' :: u.g4 ++ '-' :: u.g5

/-- Read a UUID: drop the hyphens, lower-case, cut into groups. -/
def parseUUID (t : List Char) : Option UUID :=
  let d := (t.filter (· != '-')).map lowerHex
  if h : d.length = 32 ∧ ∀ c ∈ d, isLowerHex c = true then
    some { g1 := d.take 8, g2 := (d.drop 8).take 4, g3 := (d.drop 12).take 4,
           g4 := (d.drop 16).take 4, g5 := d.drop 20
           len := by simp [h.1]
           hex := by
             intro c hc
             apply h.2
             have : d.take 8 ++ (d.drop 8).take 4 ++ (d.drop 12).take 4 ++ (d.drop 16).take 4 ++
                 d.drop 20 = d := by
               have e1 := List.take_append_drop 8 d
               have e2 := List.take_append_drop 4 (d.drop 8)
               have e3 := List.take_append_drop 4 (d.drop 12)
               have e4 := List.take_append_drop 4 (d.drop 16)
               simp only [List.drop_drop] at e2 e3 e4
               rw [List.append_assoc, List.append_assoc, List.append_assoc, e4, e3, e2, e1]
             rwa [this] at hc }
  else none

theorem hexGroups_char : ∀ (ns : List Nat) (t : List Char), hexGroups ns t = true →
    ∀ c ∈ t, isHex c = true ∨ c = '-'
  | [], t, h, c, hc => by simp [hexGroups] at h; simp [h] at hc
  | n :: ns, t, h, c, hc => by
    simp only [hexGroups, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨_, hhex⟩, hrest⟩ := h
    rw [← List.take_append_drop n t] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl (hhex c hc)
    · revert hrest hc
      cases t.drop n with
      | nil => simp
      | cons x r =>
        intro hrest hc
        by_cases hx : x = '-'
        · subst hx
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hrest
          rcases List.mem_cons.1 hc with rfl | hc
          · exact Or.inr rfl
          · exact hexGroups_char ns r hrest.2 c hc
        · have hrest' : hexGroups ns (x :: r) = true := by
            revert hrest; split
            · rename_i r' heq; simp at heq; exact absurd heq.1 hx
            · exact id
          exact hexGroups_char ns (x :: r) hrest' c hc

theorem hexGroups_cons_hyphen {n : Nat} {ns : List Nat} {g r : List Char} (hg : g.length = n)
    (hh : ∀ c ∈ g, isHex c = true) (hns : ns ≠ []) (hr : hexGroups ns r = true) :
    hexGroups (n :: ns) (g ++ '-' :: r) = true := by
  simp only [hexGroups, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  rw [List.take_left' hg, List.drop_left' hg]
  refine ⟨⟨hg, hh⟩, ?_⟩
  simp [hns, hr]

theorem hexGroups_last {n : Nat} {g : List Char} (hg : g.length = n) (hh : ∀ c ∈ g, isHex c = true) :
    hexGroups [n] g = true := by
  simp only [hexGroups, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
  exact ⟨⟨hg, hh⟩, rfl⟩

theorem filter_hyphen_of_hex {g : List Char} (h : ∀ c ∈ g, isLowerHex c = true) :
    g.filter (· != '-') = g := by
  rw [List.filter_eq_self]
  intro c hc
  simpa using ne_hyphen_of_isHex (isHex_of_lower (h c hc))

theorem map_lowerHex {g : List Char} (h : ∀ c ∈ g, isLowerHex c = true) : g.map lowerHex = g := by
  conv => rhs; rw [← List.map_id g]
  exact List.map_congr_left fun c hc => lowerHex_of_lower (h c hc)

/-- `uuid`: the UUID shape, either case, hyphens optional; rendered lower case
and hyphenated. -/
@[reducible] def uuid : Convertor where
  name := "uuid"
  Val := UUID
  accepts := uuidShape
  parse := parseUUID
  render := renderUUID
  Valid _ := True
  accepts_render u _ := by
    obtain ⟨l1, l2, l3, l4, l5⟩ := u.len
    have hx : ∀ c ∈ u.g1 ++ u.g2 ++ u.g3 ++ u.g4 ++ u.g5, isHex c = true :=
      fun c hc => isHex_of_lower (u.hex c hc)
    simp only [List.mem_append] at hx
    unfold uuidShape renderUUID
    simp only [List.append_assoc, List.cons_append]
    apply hexGroups_cons_hyphen l1 (fun c h => hx c (by simp [h])) (by simp)
    apply hexGroups_cons_hyphen l2 (fun c h => hx c (by simp [h])) (by simp)
    apply hexGroups_cons_hyphen l3 (fun c h => hx c (by simp [h])) (by simp)
    apply hexGroups_cons_hyphen l4 (fun c h => hx c (by simp [h])) (by simp)
    exact hexGroups_last l5 (fun c h => hx c (by simp [h]))
  parse_render u _ := by
    obtain ⟨g1, g2, g3, g4, g5, ⟨l1, l2, l3, l4, l5⟩, hex⟩ := u
    have hall : ∀ c ∈ g1 ++ g2 ++ g3 ++ g4 ++ g5, isLowerHex c = true := hex
    have hf : (renderUUID ⟨g1, g2, g3, g4, g5, ⟨l1, l2, l3, l4, l5⟩, hex⟩).filter (· != '-') =
        g1 ++ g2 ++ g3 ++ g4 ++ g5 := by
      simp only [renderUUID, List.filter_append, List.filter_cons]
      simp only [List.mem_append] at hall
      rw [filter_hyphen_of_hex (fun c h => hall c (by simp [h])),
        filter_hyphen_of_hex (fun c h => hall c (by simp [h])),
        filter_hyphen_of_hex (fun c h => hall c (by simp [h])),
        filter_hyphen_of_hex (fun c h => hall c (by simp [h])),
        filter_hyphen_of_hex (fun c h => hall c (by simp [h]))]
      simp
    simp only [parseUUID, hf, map_lowerHex hall]
    have hlen : (g1 ++ g2 ++ g3 ++ g4 ++ g5).length = 32 := by simp [l1, l2, l3, l4, l5]
    rw [dite_eq_left ⟨hlen, hall⟩]
    simp only [Option.some.injEq, UUID.mk.injEq]
    simp only [List.append_assoc]
    refine ⟨List.take_left' l1, ?_, ?_, ?_, ?_⟩
    · rw [List.drop_left' l1, List.take_left' l2]
    · rw [show 12 = g1.length + g2.length by omega, ← List.drop_drop, List.drop_left,
        List.drop_left, List.take_left' l3]
    · rw [show 16 = g1.length + g2.length + g3.length by omega, ← List.drop_drop, ← List.drop_drop,
        List.drop_left, List.drop_left, List.drop_left, List.take_left' l4]
    · rw [show 20 = g1.length + g2.length + g3.length + g4.length by omega, ← List.drop_drop,
        ← List.drop_drop, ← List.drop_drop, List.drop_left, List.drop_left, List.drop_left,
        List.drop_left]
  segment := true
  segment_spec _ t h hs := by
    rcases hexGroups_char _ t h '/' hs with h' | h'
    · exact ne_slash_of_isHex h' rfl
    · cases h'

/-- The built-in convertors, by name (starlette's `CONVERTOR_TYPES`). -/
def builtin : List Convertor := [str, path, int, float, uuid]

end Convertor

end Keel
