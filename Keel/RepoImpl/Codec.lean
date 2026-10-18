import Keel.DataTypes.Codec
import Keel.Proofs.Parse

/-!
# Codec combinators

Each combinator builds its decoder from its parts' decoders with `Keel.Parse`
combinators, and proves its law from its parts' laws. The proofs are where
the round trip is established, once for each combinator; any codec built
from them is lawful by construction.

Combinators: `pure`, `unit`, `token`, `lit`, `rest`, `seq`, `left`, `right`,
`map` (along a left inverse), `refine` (to a subtype), `sigma` (choice by a
decoded tag), `sum` (choice by literal tags), `delimited`, `lengthPrefixed`,
`many` (to the end of input) and `manyTill` (to a terminator).
-/

namespace Keel

open Parser

/-! ## A loop lemma

`many step` reads a concatenation of pieces when `step` reads each piece,
and consumes nothing where the pieces stop. -/

/-- `step` reads the pieces `xs` in turn, each non-empty, and then makes no
progress on `stop`. -/
def Parser.ReadsAll {τ ε α : Type} (step : Parser τ ε α) (enc : α → List τ) (stop : List τ) :
    List α → Prop
  | [] => (step.parse stop).rest.length = stop.length
  | x :: xs => enc x ≠ [] ∧ step.parse (enc x ++ (xs.flatMap enc ++ stop)) = .ok x (xs.flatMap enc ++ stop) ∧
      Parser.ReadsAll step enc stop xs

theorem Parser.parse_many_flatMap {τ ε α : Type} (step : Parser τ ε α) (enc : α → List τ)
    (stop : List τ) : ∀ xs : List α, step.ReadsAll enc stop xs →
      (many step).parse (xs.flatMap enc ++ stop) = .ok xs stop
  | [], h => by
    rw [List.flatMap_nil, List.nil_append, parse_many]
    simp only [ReadsAll] at h
    cases hc : step.parse stop with
    | ok a r => rw [hc] at h; simp [Reply.rest] at h; simp [h]
    | error e r => rw [hc] at h; simp [Reply.rest] at h; simp [h]
  | x :: xs, ⟨hne, hx, hxs⟩ => by
    rw [List.flatMap_cons, List.append_assoc, parse_many_cons step hx (by simp; exact List.length_pos_iff.mpr hne),
      parse_many_flatMap step enc stop xs hxs]
    rfl

namespace Codec

variable {τ α β : Type}

/-- Decode from a list: the value and what is left, or `none`. -/
def decode (c : Codec τ α) (l : List τ) : Option (α × List τ) :=
  match (c.parser (ε := Unit)).parse l with
  | .ok a r => some (a, r)
  | .error _ _ => none

/-- **The codec law**, as users cite it. -/
theorem decode_encode (c : Codec τ α) {a : α} {rest : List τ} (hv : c.valid a)
    (hf : c.follow rest) : c.decode (c.encode a ++ rest) = some (a, rest) := by
  simp [decode, c.parse_encode a rest hv hf]

/-- Encoding is injective on valid values (given that the end of input is a
tolerated continuation, as it is for every codec here). -/
theorem encode_injective (c : Codec τ α) (h0 : c.follow []) {a b : α} (ha : c.valid a)
    (hb : c.valid b) (h : c.encode a = c.encode b) : a = b := by
  have h1 := c.decode_encode ha h0
  rw [h, c.decode_encode hb h0] at h1
  simpa using h1.symm

/-! ## Elementary codecs -/

/-- The constant `a`, encoded as nothing. -/
protected def pure (a : α) : Codec τ α where
  encode _ := []
  parser := pure a
  valid x := x = a
  follow _ := True
  parse_encode x r hv _ := by subst hv; simp

/-- `()`, encoded as nothing. -/
def unit : Codec τ Unit where
  encode _ := []
  parser := pure ()
  valid _ := True
  follow _ := True
  parse_encode _ r _ _ := by simp

/-- One token, as itself. -/
def token : Codec τ τ where
  encode t := [t]
  parser := next
  valid _ := True
  follow _ := True
  parse_encode t r _ _ := by simp

/-- A fixed literal, carrying no information. -/
def lit [DecidableEq τ] (l : List τ) : Codec τ Unit where
  encode _ := l
  parser := Parser.lit l
  valid _ := True
  follow _ := True
  parse_encode _ r _ _ := parse_lit l r

/-- All the remaining tokens, as they are. Only the end of input may follow. -/
def rest : Codec τ (List τ) where
  encode l := l
  parser := takeWhile fun _ => true
  valid _ := True
  follow r := r = []
  parse_encode l r _ hr := by
    subst hr
    simp only [List.append_nil, parse_takeWhile, Reply.ok.injEq]
    induction l <;> simp_all

/-! ## Sequencing -/

/-- One value, then another. The first codec must tolerate what the second
writes: that is the cross condition in `valid`, and it is `True` whenever
the first codec is prefix-free. -/
def seq (c : Codec τ α) (d : Codec τ β) : Codec τ (α × β) where
  encode p := c.encode p.1 ++ d.encode p.2
  parser := do
    let a ← c.parser
    let b ← d.parser
    pure (a, b)
  valid p := c.valid p.1 ∧ d.valid p.2 ∧ ∀ r, d.follow r → c.follow (d.encode p.2 ++ r)
  follow := d.follow
  parse_encode p r hv hf := by
    obtain ⟨hva, hvb, hx⟩ := hv
    rw [List.append_assoc, parse_bind, c.parse_encode _ _ hva (hx r hf)]
    simp [d.parse_encode _ _ hvb hf]

/-- A value, then a fixed part (a separator, a terminator). -/
def left (c : Codec τ α) (d : Codec τ Unit) : Codec τ α where
  encode a := c.encode a ++ d.encode ()
  parser := c.parser <* d.parser
  valid a := c.valid a ∧ d.valid () ∧ ∀ r, d.follow r → c.follow (d.encode () ++ r)
  follow := d.follow
  parse_encode a r hv hf := by
    obtain ⟨hva, hvb, hx⟩ := hv
    rw [List.append_assoc, parse_seqLeft, c.parse_encode _ _ hva (hx r hf)]
    simp [d.parse_encode _ _ hvb hf]

/-- A fixed part (a tag, an opening delimiter), then a value. -/
def right (d : Codec τ Unit) (c : Codec τ α) : Codec τ α where
  encode a := d.encode () ++ c.encode a
  parser := d.parser *> c.parser
  valid a := d.valid () ∧ c.valid a ∧ ∀ r, c.follow r → d.follow (c.encode a ++ r)
  follow := c.follow
  parse_encode a r hv hf := by
    obtain ⟨hvd, hva, hx⟩ := hv
    rw [List.append_assoc, parse_seqRight, d.parse_encode _ _ hvd (hx r hf)]
    simp [c.parse_encode _ _ hva hf]

/-! ## Changing the value type -/

/-- Along a map `f` with a right inverse `g` (`f (g b) = b`): decode an `α` and
apply `f`, encode `b` as `g b`. An equivalence is the common case. -/
def map (c : Codec τ α) (f : α → β) (g : β → α) (h : Function.LeftInverse f g) : Codec τ β where
  encode b := c.encode (g b)
  parser := f <$> c.parser
  valid b := c.valid (g b)
  follow := c.follow
  parse_encode b r hv hf := by simp [c.parse_encode _ _ hv hf, h b]

/-- The values satisfying `P`: decoding checks `P` (failing with
`unexpected` otherwise), and the decoded value carries the proof. -/
def refine (c : Codec τ α) (P : α → Prop) [DecidablePred P] : Codec τ {a // P a} where
  encode x := c.encode x.1
  parser := do
    let a ← c.parser
    if h : P a then pure ⟨a, h⟩ else fail ParseError.unexpected
  valid x := c.valid x.1
  follow := c.follow
  parse_encode x r hv hf := by simp [c.parse_encode _ _ hv hf, x.2]

/-! ## Choice -/

/-- **Choice by tag.** A tag `t`, then a value of the type the tag selects. -/
def sigma {T : Type} {β : T → Type} (tag : Codec τ T) (body : (t : T) → Codec τ (β t)) :
    Codec τ (Σ t, β t) where
  encode p := tag.encode p.1 ++ (body p.1).encode p.2
  parser := do
    let t ← tag.parser
    let b ← (body t).parser
    pure ⟨t, b⟩
  valid p := tag.valid p.1 ∧ (body p.1).valid p.2 ∧
    ∀ r, (body p.1).follow r → tag.follow ((body p.1).encode p.2 ++ r)
  follow r := ∀ t, (body t).follow r
  parse_encode p r hv hf := by
    obtain ⟨t, b⟩ := p
    obtain ⟨hvt, hvb, hx⟩ := hv
    rw [List.append_assoc, parse_bind, tag.parse_encode _ _ hvt (hx r (hf t))]
    simp [(body t).parse_encode _ _ hvb (hf t)]

theorem not_prefix_append_of_incomparable {l m x : List τ} (h : Incomparable l m) :
    ¬ l <+: m ++ x := by
  intro hl
  rcases List.prefix_or_prefix_of_prefix hl (List.prefix_append m x) with h' | h'
  · exact h.1 h'
  · exact h.2 h'

/-- **Choice by literal tags.** `tl` then a left value, or `tr` then a right
value. The tags must be prefix-incomparable, so each is recognised without
backtracking; for concrete tags `decide` proves it. -/
def sum [DecidableEq τ] (tl tr : List τ) (c : Codec τ α) (d : Codec τ β)
    (htag : Incomparable tl tr := by decide) : Codec τ (α ⊕ β) where
  encode
    | .inl a => tl ++ c.encode a
    | .inr b => tr ++ d.encode b
  parser := (Parser.lit tl *> (Sum.inl <$> c.parser)) <|> (Parser.lit tr *> (Sum.inr <$> d.parser))
  valid
    | .inl a => c.valid a
    | .inr b => d.valid b
  follow r := c.follow r ∧ d.follow r
  parse_encode := @fun ε _ x r hv hf => by
    cases x with
    | inl a =>
      simp only
      rw [parse_orElse, List.append_assoc, parse_seqRight, parse_lit]
      simp [c.parse_encode _ _ hv hf.1]
    | inr b =>
      simp only
      rw [parse_orElse, parse_seqRight, List.append_assoc]
      cases hl : (Parser.lit tl : Parser τ ε Unit).parse (tr ++ (d.encode b ++ r)) with
      | ok u r' =>
        exact absurd ⟨r', ((parse_lit_ok).1 hl).symm⟩ (not_prefix_append_of_incomparable htag)
      | error e r' =>
        have := parse_lit_error hl; subst this
        simp [d.parse_encode _ _ hv hf.2]

/-! ## Framing -/

/-- The scan of `delimited`: tokens up to the first occurrence of `d`. -/
def scanTo [DecidableEq τ] {ε : Type} [ParseError ε] (d : List τ) : Parser τ ε (List τ) :=
  many (notFollowedBy (Parser.lit d) *> next)

theorem avoids_tail {d : List τ} {t : τ} {l : List τ} (h : Avoids d (t :: l)) : Avoids d l := by
  intro k hk
  have := h (k + 1) (by simp; omega)
  simpa using this

theorem not_prefix_of_avoids {d : List τ} {l : List τ} (h : Avoids d l) (hl : l ≠ []) (r : List τ) :
    ¬ d <+: l ++ d ++ r := by
  intro hp
  apply h 0 (List.length_pos_iff.mpr hl)
  simp only [List.drop_zero]
  exact List.prefix_of_prefix_length_le hp (List.prefix_append _ _) (by simp)

theorem readsAll_scanTo [DecidableEq τ] {ε : Type} [ParseError ε] (d r : List τ) :
    ∀ l : List τ, Avoids d l →
      (notFollowedBy (Parser.lit d) *> next : Parser τ ε τ).ReadsAll (fun t => [t]) (d ++ r) l
  | [], _ => by
    simp only [Parser.ReadsAll, parse_seqRight, parse_notFollowedBy, parse_lit, Reply.bind_error,
      Reply.rest]
  | t :: l, hl => by
    refine ⟨by simp, ?_, readsAll_scanTo d r l (avoids_tail hl)⟩
    have hnp := not_prefix_of_avoids hl (by simp) r
    simp only [List.flatMap_singleton', List.cons_append]
    rw [parse_seqRight, parse_notFollowedBy]
    cases hc : (Parser.lit d : Parser τ ε Unit).parse (t :: (l ++ (d ++ r))) with
    | ok u r' =>
      exfalso; apply hnp
      have := (parse_lit_ok).1 hc
      exact ⟨r', by simp only [List.cons_append, List.append_assoc] at this ⊢; exact this.symm⟩
    | error e r' => simp [hc]

theorem parse_scanTo [DecidableEq τ] {ε : Type} [ParseError ε] (d r l : List τ) (hl : Avoids d l) :
    (scanTo d : Parser τ ε (List τ)).parse (l ++ (d ++ r)) = .ok l (d ++ r) := by
  have key := Parser.parse_many_flatMap (notFollowedBy (Parser.lit d) *> next : Parser τ ε τ)
    (fun t => [t]) (d ++ r) l (readsAll_scanTo d r l hl)
  simpa [scanTo] using key

/-- **Delimited.** A value whose encoding is followed by the delimiter `d`.
The decoder finds the first `d`, decodes the tokens before it with `c` alone
(they must be all of `c`'s encoding), and consumes `d`. The value is valid
when its encoding *avoids* `d`: that is the escaping side condition, which an
escaping encoder establishes once. -/
def delimited [DecidableEq τ] (d : List τ) (c : Codec τ α) : Codec τ α where
  encode a := c.encode a ++ d
  parser := do
    let n ← lookahead (List.length <$> scanTo d)
    let a ← isolate n c.parser
    Parser.lit d
    pure a
  valid a := c.valid a ∧ c.follow [] ∧ Avoids d (c.encode a)
  follow _ := True
  parse_encode := @fun ε _ a r hv _ => by
    obtain ⟨hva, hf0, hav⟩ := hv
    rw [List.append_assoc]
    simp only [parse_bind, parse_lookahead, parse_map, parse_scanTo (ε := ε) d r _ hav, Reply.map_ok,
      Reply.bind_ok]
    rw [parse_isolate_append rfl (by simpa using c.parse_encode a [] hva hf0)]
    simp

/-- **Length-prefixed.** The length of the encoding, by `len`, then the
encoding. The decoder reads exactly that many tokens with `c`. -/
def lengthPrefixed (len : Codec τ Nat) (c : Codec τ α) : Codec τ α where
  encode a := len.encode (c.encode a).length ++ c.encode a
  parser := do
    let n ← len.parser
    isolate n c.parser
  valid a := c.valid a ∧ c.follow [] ∧ len.valid (c.encode a).length ∧
    ∀ r, len.follow (c.encode a ++ r)
  follow _ := True
  parse_encode a r hv _ := by
    obtain ⟨hva, hf0, hvl, hfl⟩ := hv
    rw [List.append_assoc, parse_bind, len.parse_encode _ _ hvl (hfl r)]
    simp only [Reply.bind_ok]
    exact parse_isolate_append rfl (by simpa using c.parse_encode a [] hva hf0)

/-! ## Repetition -/

/-- The values `many c` round-trips: each valid, each encoding non-empty, and
each tolerating what follows it (the rest of the list). -/
def ManyValid (c : Codec τ α) : List α → Prop
  | [] => True
  | x :: xs => c.valid x ∧ c.encode x ≠ [] ∧ c.follow (xs.flatMap c.encode) ∧ ManyValid c xs

/-- **Many, to the end.** The values one after another, filling the input. -/
def many (c : Codec τ α) : Codec τ (List α) where
  encode xs := xs.flatMap c.encode
  parser := Parser.many c.parser
  valid := ManyValid c
  follow r := r = []
  parse_encode := @fun ε _ xs r hv hr => by
    subst hr
    apply Parser.parse_many_flatMap
    induction xs with
    | nil =>
      have := Parser.parse_rest_suffix (c.parser (ε := ε)) []
      simp only [List.suffix_nil] at this
      simp [Parser.ReadsAll, this]
    | cons x xs ih =>
      obtain ⟨hvx, hne, hfx, hvs⟩ := hv
      exact ⟨hne, by simpa using c.parse_encode x _ hvx (by simpa using hfx), ih hvs⟩

/-- The values `manyTill c term` round-trips: each valid, each encoding
prefix-incomparable with the terminator (so the decoder can tell them apart),
and each tolerating what follows it. -/
def ManyTillValid (c : Codec τ α) (term : List τ) : List α → Prop
  | [] => True
  | x :: xs => c.valid x ∧ Incomparable term (c.encode x) ∧
      (∀ r, c.follow (xs.flatMap c.encode ++ term ++ r)) ∧ ManyTillValid c term xs

/-- **Many, with a terminator.** The values one after another, then `term`. -/
def manyTill [DecidableEq τ] (c : Codec τ α) (term : List τ) : Codec τ (List α) where
  encode xs := xs.flatMap c.encode ++ term
  parser := do
    let xs ← Parser.many (notFollowedBy (Parser.lit term) *> c.parser)
    Parser.lit term
    pure xs
  valid := ManyTillValid c term
  follow _ := True
  parse_encode := @fun ε _ xs r hv _ => by
    rw [List.append_assoc, parse_bind, Parser.parse_many_flatMap _ c.encode (term ++ r) xs]
    · simp
    induction xs with
    | nil => simp [Parser.ReadsAll, Reply.rest]
    | cons x xs ih =>
      obtain ⟨hvx, hinc, hfx, hvs⟩ := hv
      have hne : c.encode x ≠ [] := by
        rintro h; rw [h] at hinc; exact hinc.2 (List.nil_prefix)
      refine ⟨hne, ?_, ih hvs⟩
      rw [parse_seqRight, parse_notFollowedBy]
      cases hc : (Parser.lit term : Parser τ ε Unit).parse (c.encode x ++ (xs.flatMap c.encode ++ (term ++ r))) with
      | ok u r' =>
        exact absurd ⟨r', ((parse_lit_ok).1 hc).symm⟩ (not_prefix_append_of_incomparable hinc)
      | error e r' =>
        simp only [Reply.bind_ok]
        rw [c.parse_encode _ _ hvx (by simpa [List.append_assoc] using hfx r)]

end Codec

end Keel
