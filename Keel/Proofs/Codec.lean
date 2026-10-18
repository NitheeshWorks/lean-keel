import Keel.RepoImpl.CodecBasic

/-!
# Proofs: the laws of `Keel.Codec`, per combinator

Each combinator's law is the general `Codec.decode_encode` read at that
combinator, with its `valid` and `follow` conditions spelled out. They are
one-liners because the work happened once, in the combinator's construction
(`RepoImpl/Codec.lean`). Downstream codecs built from these get the same
law, with no proof of their own.
-/

namespace Keel

namespace Codec

variable {τ α β : Type}

/-! ## Encodings, by combinator -/

@[simp] theorem seq_encode (c : Codec τ α) (d : Codec τ β) (a : α) (b : β) :
    (c.seq d).encode (a, b) = c.encode a ++ d.encode b := rfl
@[simp] theorem left_encode (c : Codec τ α) (d : Codec τ Unit) (a : α) :
    (c.left d).encode a = c.encode a ++ d.encode () := rfl
@[simp] theorem right_encode (d : Codec τ Unit) (c : Codec τ α) (a : α) :
    (d.right c).encode a = d.encode () ++ c.encode a := rfl
@[simp] theorem map_encode (c : Codec τ α) (f : α → β) (g : β → α) (h : Function.LeftInverse f g)
    (b : β) : (c.map f g h).encode b = c.encode (g b) := rfl
@[simp] theorem refine_encode (c : Codec τ α) (P : α → Prop) [DecidablePred P] (x : {a // P a}) :
    (c.refine P).encode x = c.encode x.1 := rfl
@[simp] theorem lit_encode [DecidableEq τ] (l : List τ) (u : Unit) : (lit l).encode u = l := rfl
@[simp] theorem token_encode (t : τ) : (token : Codec τ τ).encode t = [t] := rfl
@[simp] theorem rest_encode (l : List τ) : (rest : Codec τ (List τ)).encode l = l := rfl
@[simp] theorem delimited_encode [DecidableEq τ] (d : List τ) (c : Codec τ α) (a : α) :
    (delimited d c).encode a = c.encode a ++ d := rfl
@[simp] theorem lengthPrefixed_encode (len : Codec τ Nat) (c : Codec τ α) (a : α) :
    (lengthPrefixed len c).encode a = len.encode (c.encode a).length ++ c.encode a := rfl
@[simp] theorem many_encode (c : Codec τ α) (xs : List α) :
    c.many.encode xs = xs.flatMap c.encode := rfl
@[simp] theorem manyTill_encode [DecidableEq τ] (c : Codec τ α) (term : List τ) (xs : List α) :
    (c.manyTill term).encode xs = xs.flatMap c.encode ++ term := rfl
@[simp] theorem sum_encode_inl [DecidableEq τ] (tl tr : List τ) (c : Codec τ α) (d : Codec τ β)
    (h : Incomparable tl tr) (a : α) : (sum tl tr c d h).encode (.inl a) = tl ++ c.encode a := rfl
@[simp] theorem sum_encode_inr [DecidableEq τ] (tl tr : List τ) (c : Codec τ α) (d : Codec τ β)
    (h : Incomparable tl tr) (b : β) : (sum tl tr c d h).encode (.inr b) = tr ++ d.encode b := rfl

/-! ## Side conditions, by combinator (for `simp`) -/

@[simp] theorem pure_valid (a x : α) : (Codec.pure a : Codec τ α).valid x ↔ x = a := Iff.rfl
@[simp] theorem pure_follow (a : α) (r : List τ) : (Codec.pure a : Codec τ α).follow r := trivial
@[simp] theorem unit_valid (u : Unit) : (unit : Codec τ Unit).valid u := trivial
@[simp] theorem unit_follow (r : List τ) : (unit : Codec τ Unit).follow r := trivial
@[simp] theorem token_valid (t : τ) : (token : Codec τ τ).valid t := trivial
@[simp] theorem token_follow (r : List τ) : (token : Codec τ τ).follow r := trivial
@[simp] theorem lit_valid [DecidableEq τ] (l : List τ) (u : Unit) : (lit l).valid u := trivial
@[simp] theorem lit_follow [DecidableEq τ] (l r : List τ) : (lit l).follow r := trivial
@[simp] theorem rest_valid (l : List τ) : (rest : Codec τ (List τ)).valid l := trivial
@[simp] theorem rest_follow (r : List τ) : (rest : Codec τ (List τ)).follow r ↔ r = [] := Iff.rfl
@[simp] theorem seq_valid (c : Codec τ α) (d : Codec τ β) (p : α × β) :
    (c.seq d).valid p ↔ c.valid p.1 ∧ d.valid p.2 ∧ ∀ r, d.follow r → c.follow (d.encode p.2 ++ r) :=
  Iff.rfl
@[simp] theorem seq_follow (c : Codec τ α) (d : Codec τ β) (r : List τ) :
    (c.seq d).follow r ↔ d.follow r := Iff.rfl
@[simp] theorem left_valid (c : Codec τ α) (d : Codec τ Unit) (a : α) :
    (c.left d).valid a ↔ c.valid a ∧ d.valid () ∧ ∀ r, d.follow r → c.follow (d.encode () ++ r) :=
  Iff.rfl
@[simp] theorem left_follow (c : Codec τ α) (d : Codec τ Unit) (r : List τ) :
    (c.left d).follow r ↔ d.follow r := Iff.rfl
@[simp] theorem right_valid (d : Codec τ Unit) (c : Codec τ α) (a : α) :
    (d.right c).valid a ↔ d.valid () ∧ c.valid a ∧ ∀ r, c.follow r → d.follow (c.encode a ++ r) :=
  Iff.rfl
@[simp] theorem right_follow (d : Codec τ Unit) (c : Codec τ α) (r : List τ) :
    (d.right c).follow r ↔ c.follow r := Iff.rfl
@[simp] theorem map_valid (c : Codec τ α) (f : α → β) (g : β → α) (h : Function.LeftInverse f g)
    (b : β) : (c.map f g h).valid b ↔ c.valid (g b) := Iff.rfl
@[simp] theorem map_follow (c : Codec τ α) (f : α → β) (g : β → α) (h : Function.LeftInverse f g)
    (r : List τ) : (c.map f g h).follow r ↔ c.follow r := Iff.rfl
@[simp] theorem refine_valid (c : Codec τ α) (P : α → Prop) [DecidablePred P] (x : {a // P a}) :
    (c.refine P).valid x ↔ c.valid x.1 := Iff.rfl
@[simp] theorem refine_follow (c : Codec τ α) (P : α → Prop) [DecidablePred P] (r : List τ) :
    (c.refine P).follow r ↔ c.follow r := Iff.rfl
@[simp] theorem delimited_valid [DecidableEq τ] (d : List τ) (c : Codec τ α) (a : α) :
    (delimited d c).valid a ↔ c.valid a ∧ c.follow [] ∧ Avoids d (c.encode a) := Iff.rfl
@[simp] theorem delimited_follow [DecidableEq τ] (d : List τ) (c : Codec τ α) (r : List τ) :
    (delimited d c).follow r := trivial
@[simp] theorem lengthPrefixed_valid (len : Codec τ Nat) (c : Codec τ α) (a : α) :
    (lengthPrefixed len c).valid a ↔ c.valid a ∧ c.follow [] ∧ len.valid (c.encode a).length ∧
      ∀ r, len.follow (c.encode a ++ r) := Iff.rfl
@[simp] theorem lengthPrefixed_follow (len : Codec τ Nat) (c : Codec τ α) (r : List τ) :
    (lengthPrefixed len c).follow r := trivial
@[simp] theorem many_valid (c : Codec τ α) (xs : List α) : c.many.valid xs ↔ ManyValid c xs := Iff.rfl
@[simp] theorem many_follow (c : Codec τ α) (r : List τ) : c.many.follow r ↔ r = [] := Iff.rfl
@[simp] theorem manyTill_valid [DecidableEq τ] (c : Codec τ α) (term : List τ) (xs : List α) :
    (c.manyTill term).valid xs ↔ ManyTillValid c term xs := Iff.rfl
@[simp] theorem manyTill_follow [DecidableEq τ] (c : Codec τ α) (term r : List τ) :
    (c.manyTill term).follow r := trivial
@[simp] theorem nat_valid (n : Nat) : nat.valid n := trivial
@[simp] theorem nat_follow (r : List Char) : nat.follow r ↔ NoDigitNext r := Iff.rfl
@[simp] theorem natBE_valid (w n : Nat) : (natBE w).valid n ↔ n < 256 ^ w := Iff.rfl
@[simp] theorem natBE_follow (w : Nat) (r : List UInt8) : (natBE w).follow r := trivial
@[simp] theorem nat_encode (n : Nat) : nat.encode n = decimal n := rfl
@[simp] theorem natBE_encode (w n : Nat) : (natBE w).encode n = beBytes w n := rfl
@[simp] theorem string_valid (s : String) : string.valid s := trivial
@[simp] theorem string_follow (r : List Char) : string.follow r ↔ r = [] := Iff.rfl
@[simp] theorem string_encode (s : String) : string.encode s = s.toList := rfl
@[simp] theorem bytes_valid (b : ByteArray) : bytes.valid b := trivial
@[simp] theorem bytes_follow (r : List UInt8) : bytes.follow r ↔ r = [] := Iff.rfl
@[simp] theorem bytes_encode (b : ByteArray) : bytes.encode b = b.data.toList := rfl
@[simp] theorem noDigitNext_nil : NoDigitNext [] := by intro c h; cases h
@[simp] theorem noDigitNext_cons (c : Char) (r : List Char) :
    NoDigitNext (c :: r) ↔ c.isDigit = false := by
  constructor
  · intro h; exact h c rfl
  · intro h c' hc; cases hc; exact h

@[simp] theorem manyValid_nil (c : Codec τ α) : ManyValid c [] := trivial
@[simp] theorem manyValid_cons (c : Codec τ α) (x : α) (xs : List α) :
    ManyValid c (x :: xs) ↔
      c.valid x ∧ c.encode x ≠ [] ∧ c.follow (xs.flatMap c.encode) ∧ ManyValid c xs := Iff.rfl
@[simp] theorem manyTillValid_nil (c : Codec τ α) (term : List τ) : ManyTillValid c term [] := trivial
@[simp] theorem manyTillValid_cons (c : Codec τ α) (term : List τ) (x : α) (xs : List α) :
    ManyTillValid c term (x :: xs) ↔
      c.valid x ∧ Incomparable term (c.encode x) ∧
        (∀ r, c.follow (xs.flatMap c.encode ++ term ++ r)) ∧ ManyTillValid c term xs := Iff.rfl

/-! ## The side conditions, made easy -/

/-- A delimiter whose first token never occurs in the encoding is avoided.
This is how a line, a header field or a base64 token meets `delimited`'s
side condition. -/
theorem avoids_of_head_not_mem {d l : List τ} {x : τ} (hd : d.head? = some x) (hx : x ∉ l) :
    Avoids d l := by
  intro k hk hp
  obtain ⟨d', rfl⟩ : ∃ d', d = x :: d' := by
    cases d with
    | nil => simp at hd
    | cons y d' => simp at hd; exact ⟨d', by rw [hd]⟩
  have hget := hp.getElem (i := 0) (by simp)
  simp only [List.getElem_cons_zero, List.getElem_drop, Nat.add_zero] at hget
  rw [List.getElem_append_left hk] at hget
  exact hx (hget ▸ List.getElem_mem hk)

/-- Two tags that differ in their first token are incomparable. -/
theorem incomparable_of_head_ne {t u : τ} {l m : List τ} (h : t ≠ u) :
    Incomparable (t :: l) (u :: m) := by
  constructor
  · intro hp; exact h (List.cons_prefix_cons.1 hp).1
  · intro hp; exact h (List.cons_prefix_cons.1 hp).1.symm

/-! ## The laws, by combinator -/

theorem pure_lawful (a : α) (r : List τ) : (Codec.pure a : Codec τ α).decode r = some (a, r) := by
  have := (Codec.pure a : Codec τ α).decode_encode (a := a) (rest := r) rfl trivial
  exact this

theorem token_lawful (t : τ) (r : List τ) : (token : Codec τ τ).decode (t :: r) = some (t, r) :=
  token.decode_encode (a := t) trivial trivial

theorem lit_lawful [DecidableEq τ] (l r : List τ) : (lit l).decode (l ++ r) = some ((), r) :=
  (lit l).decode_encode (a := ()) trivial trivial

theorem rest_lawful (l : List τ) : (rest : Codec τ (List τ)).decode l = some (l, []) := by
  simpa using (rest : Codec τ (List τ)).decode_encode (a := l) (rest := []) trivial rfl

theorem seq_lawful (c : Codec τ α) (d : Codec τ β) {a : α} {b : β} {r : List τ}
    (ha : c.valid a) (hb : d.valid b) (hx : ∀ r, d.follow r → c.follow (d.encode b ++ r))
    (hr : d.follow r) :
    (c.seq d).decode (c.encode a ++ d.encode b ++ r) = some ((a, b), r) :=
  (c.seq d).decode_encode (a := (a, b)) ⟨ha, hb, hx⟩ hr

theorem map_lawful (c : Codec τ α) (f : α → β) (g : β → α) (h : Function.LeftInverse f g)
    {b : β} {r : List τ} (hb : c.valid (g b)) (hr : c.follow r) :
    (c.map f g h).decode (c.encode (g b) ++ r) = some (b, r) :=
  (c.map f g h).decode_encode hb hr

theorem refine_lawful (c : Codec τ α) (P : α → Prop) [DecidablePred P] {x : {a // P a}}
    {r : List τ} (hx : c.valid x.1) (hr : c.follow r) :
    (c.refine P).decode (c.encode x.1 ++ r) = some (x, r) :=
  (c.refine P).decode_encode hx hr

theorem sigma_lawful {T : Type} {β : T → Type} (tag : Codec τ T) (body : (t : T) → Codec τ (β t))
    {t : T} {b : β t} {r : List τ} (ht : tag.valid t) (hb : (body t).valid b)
    (hx : ∀ r, (body t).follow r → tag.follow ((body t).encode b ++ r)) (hr : ∀ t, (body t).follow r) :
    (sigma tag body).decode (tag.encode t ++ (body t).encode b ++ r) = some (⟨t, b⟩, r) :=
  (sigma tag body).decode_encode (a := ⟨t, b⟩) ⟨ht, hb, hx⟩ hr

theorem sum_lawful_inl [DecidableEq τ] (tl tr : List τ) (c : Codec τ α) (d : Codec τ β)
    (h : Incomparable tl tr) {a : α} {r : List τ} (ha : c.valid a) (hr : c.follow r ∧ d.follow r) :
    (sum tl tr c d h).decode (tl ++ c.encode a ++ r) = some (.inl a, r) :=
  (sum tl tr c d h).decode_encode (a := .inl a) ha hr

theorem sum_lawful_inr [DecidableEq τ] (tl tr : List τ) (c : Codec τ α) (d : Codec τ β)
    (h : Incomparable tl tr) {b : β} {r : List τ} (hb : d.valid b) (hr : c.follow r ∧ d.follow r) :
    (sum tl tr c d h).decode (tr ++ d.encode b ++ r) = some (.inr b, r) :=
  (sum tl tr c d h).decode_encode (a := .inr b) hb hr

/-- **Delimited**: on any continuation, provided the encoding avoids the
delimiter. -/
theorem delimited_lawful [DecidableEq τ] (d : List τ) (c : Codec τ α) {a : α} {r : List τ}
    (ha : c.valid a) (h0 : c.follow []) (hav : Avoids d (c.encode a)) :
    (delimited d c).decode (c.encode a ++ d ++ r) = some (a, r) :=
  (delimited d c).decode_encode ⟨ha, h0, hav⟩ trivial

/-- **Length-prefixed**: on any continuation. -/
theorem lengthPrefixed_lawful (len : Codec τ Nat) (c : Codec τ α) {a : α} {r : List τ}
    (ha : c.valid a) (h0 : c.follow []) (hl : len.valid (c.encode a).length)
    (hlf : ∀ r, len.follow (c.encode a ++ r)) :
    (lengthPrefixed len c).decode (len.encode (c.encode a).length ++ c.encode a ++ r) = some (a, r) :=
  (lengthPrefixed len c).decode_encode ⟨ha, h0, hl, hlf⟩ trivial

/-- **Many, to the end.** -/
theorem many_lawful (c : Codec τ α) {xs : List α} (h : ManyValid c xs) :
    c.many.decode (xs.flatMap c.encode) = some (xs, []) := by
  simpa using c.many.decode_encode (a := xs) (rest := []) h rfl

/-- **Many, with a terminator**: on any continuation. -/
theorem manyTill_lawful [DecidableEq τ] (c : Codec τ α) (term : List τ) {xs : List α} {r : List τ}
    (h : ManyTillValid c term xs) :
    (c.manyTill term).decode (xs.flatMap c.encode ++ term ++ r) = some (xs, r) :=
  (c.manyTill term).decode_encode h trivial

/-- **Decimal**: on any continuation that does not start with a digit. -/
theorem nat_lawful (n : Nat) {r : List Char} (hr : NoDigitNext r) :
    nat.decode (decimal n ++ r) = some (n, r) :=
  nat.decode_encode (a := n) trivial hr

/-- **Big-endian**: on any continuation, for values that fit. -/
theorem natBE_lawful (w n : Nat) (r : List UInt8) (h : n < 256 ^ w) :
    (natBE w).decode (beBytes w n ++ r) = some (n, r) :=
  (natBE w).decode_encode h trivial

end Codec

end Keel
