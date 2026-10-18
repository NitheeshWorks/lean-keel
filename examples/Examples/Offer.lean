import Keel

/-!
# Example: refined types and located validation errors

STYLE.md's `Offer`: the constraints are in the field types, so an `Offer`
value cannot hold a non-positive price, and the default `0` is checked where
it is written. Raw input is validated field by field; every error says which
field failed and how, as a pydantic `ValidationError` does.

Inherits: `Constraint.validate_iff` (through `Validator.check_ok_iff`),
`Validator.both_ok_iff`, and the location laws (`Validator.loc_check`,
`Validator.both_error`): an error is always located under the field it
belongs to.
-/

namespace Examples.Offer

open Keel

structure Offer where
  price    : Int ∣ gt 0
  discount : Nat ∣ le 100 := 0

/-- Untrusted input, before validation. -/
structure RawOffer where
  price : Int
  discount : Nat

/-- Validate a raw offer: each field under its name, every failure reported. -/
def validate : Validator Refine.Issue RawOffer Offer :=
  ((Validator.field "price" (·.price) (Validator.check (.gt 0))).both
    (Validator.field "discount" (·.discount) (Validator.check (.le 100)))).map
    fun (p, d) => { price := p, discount := d }

/-- **Validation succeeds exactly when the constraints hold.** -/
theorem validate_ok_iff (raw : RawOffer) :
    (∃ o, validate raw = .ok o) ↔ 0 < raw.price ∧ raw.discount ≤ 100 := by
  constructor
  · rintro ⟨o, h⟩
    obtain ⟨⟨p, d⟩, h1, _⟩ := (Validator.map_ok_iff _ _ _ _).1 h
    obtain ⟨hp, hd⟩ := (Validator.both_ok_iff _ _ _ _ _).1 h1
    have hp' := (Validator.check_ok_iff (.gt 0) raw.price).1 ⟨p, by
      simpa [Validator.field_apply, Except.mapError] using
        (Validator.at_ok_iff _ _ _ _).1 hp⟩
    have hd' := (Validator.check_ok_iff (.le 100) raw.discount).1 ⟨d, by
      simpa [Validator.field_apply, Except.mapError] using
        (Validator.at_ok_iff _ _ _ _).1 hd⟩
    exact ⟨hp', hd'⟩
  · rintro ⟨hp, hd⟩
    obtain ⟨p, hp'⟩ := (Validator.check_ok_iff (.gt 0) raw.price).2 hp
    obtain ⟨d, hd'⟩ := (Validator.check_ok_iff (.le 100) raw.discount).2 hd
    refine ⟨{ price := p, discount := d }, (Validator.map_ok_iff _ _ _ _).2 ⟨(p, d), ?_, rfl⟩⟩
    refine (Validator.both_ok_iff _ _ _ _ _).2 ⟨?_, ?_⟩
    · exact (Validator.at_ok_iff _ _ _ _).2 hp'
    · exact (Validator.at_ok_iff _ _ _ _).2 hd'

/-- **Every error is located under its field.** -/
theorem validate_errors_located (raw : RawOffer) (es : List Refine.Issue)
    (h : validate raw = .error es) :
    ∀ e ∈ es, e.loc = [.key "price"] ∨ e.loc = [.key "discount"] := by
  have h1 := (Validator.map_error_iff _ _ _ _).1 h
  have hes := Validator.both_error _ _ _ _ h1
  intro e he
  rw [hes] at he
  rcases List.mem_append.1 he with he | he
  · left
    revert he
    cases hc : Validator.check (.gt 0) raw.price with
    | ok _ => simp [Validator.field_apply, hc, Except.mapError]
    | error es' =>
      simp only [Validator.field_apply, hc, Except.mapError, List.mem_map]
      rintro ⟨e', he', rfl⟩
      show _ :: e'.loc = _
      rw [Validator.loc_check _ _ _ hc e' he']
  · right
    revert he
    cases hc : Validator.check (.le 100) raw.discount with
    | ok _ => simp [Validator.field_apply, hc, Except.mapError]
    | error es' =>
      simp only [Validator.field_apply, hc, Except.mapError, List.mem_map]
      rintro ⟨e', he', rfl⟩
      show _ :: e'.loc = _
      rw [Validator.loc_check _ _ _ hc e' he']

/-- Both fields wrong: two errors, each at its field. -/
example : (match validate ⟨-1, 150⟩ with
    | .ok _ => []
    | .error es => es.map fun e => (e.loc, e.kind)) =
    [([.key "price"], "greater_than"), ([.key "discount"], "less_than_equal")] := by
  decide

/-! ## Running it -/

def report (r : Except (List Refine.Issue) Offer) : String :=
  match r with
  | .ok o => s!"ok: price {o.price.val}, discount {o.discount.val}"
  | .error es => ", ".intercalate (es.map fun e => s!"{repr e.loc} {e.kind} (input {e.input})")

def run : IO Unit := do
  IO.println (report (validate ⟨25, 10⟩))
  IO.println (report (validate ⟨-1, 150⟩))
  let o : Offer := { price := 3 }
  IO.println s!"default discount: {o.discount.val}"

end Examples.Offer
