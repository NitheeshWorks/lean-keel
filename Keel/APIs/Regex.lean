import Keel.Proofs.Regex

/-!
# APIs: compiled patterns

`r.compile m` compiles a pattern once for a mode, to the numbered tables of
`Nfa.build` (or the plain scan, should the numbering check fail), and gives
a `Matcher`: what it accepts is `Accepts m r`, by `Matcher.test_iff`.

A dialect's parser produces the `Regex κ`; its classes say what `\d`, `\w`
and `.` mean. Python's `re.fullmatch` is `Mode.full`, `re.match` is
`Mode.prefix`, `re.search` and Rust's `is_match` are `Mode.search`.
-/

namespace Keel

/-- A pattern compiled for a mode, with the law that it decides `Accepts`. -/
structure Regex.Matcher (κ : Type) [CharClass κ] [DecidableEq κ] where
  /-- The pattern. -/
  regex : Regex κ
  /-- Where a match may lie. -/
  mode : Regex.Mode
  /-- The compiled test, on characters. -/
  run : List Char → Bool
  run_eq : ∀ t, run t = regex.accepts mode t

namespace Regex

variable {κ : Type} [CharClass κ] [DecidableEq κ] [Hashable κ]

/-- **Compile a pattern** for a mode (the default: anywhere in the text). -/
@[specialize] def compile (r : Regex κ) (m : Mode := .search) : Matcher κ :=
  match Nfa.build r with
  | some N => ⟨r, m, N.accepts m, N.accepts_eq m⟩
  | none => ⟨r, m, r.accepts m, fun _ => rfl⟩

omit [Hashable κ] in
/-- Run a compiled pattern on a string. -/
def Matcher.test (M : Matcher κ) (s : String) : Bool := M.run s.toList

omit [Hashable κ] in
/-- **A compiled pattern decides acceptance.** -/
theorem Matcher.test_iff (M : Matcher κ) (s : String) :
    M.test s = true ↔ Accepts M.mode M.regex s.toList := by
  rw [Matcher.test, M.run_eq, accepts_iff]

theorem compile_regex (r : Regex κ) (m : Mode) : (r.compile m).regex = r := by
  unfold compile; split <;> rfl

theorem compile_mode (r : Regex κ) (m : Mode) : (r.compile m).mode = m := by
  unfold compile; split <;> rfl

/-- **What a compiled pattern accepts**: the segments the mode allows that
`r` matches. -/
theorem compile_test_iff (r : Regex κ) (m : Mode) (s : String) :
    (r.compile m).test s = true ↔ Accepts m r s.toList := by
  rw [Matcher.test_iff, compile_regex, compile_mode]

omit [Hashable κ] in
/-- `fullmatch`: the whole text matches. -/
theorem accepts_full_iff (r : Regex κ) (t : List Char) :
    r.accepts .full t = true ↔ Matches r none t none := by
  rw [accepts_iff]
  constructor
  · rintro ⟨x, y, rfl, hy, u, v, rfl, hu, hm⟩
    obtain rfl := hy rfl; obtain rfl := hu rfl
    simpa using hm
  · intro h
    exact ⟨t, [], by simp, fun _ => rfl, [], t, rfl, fun _ => rfl, h⟩

end Regex

end Keel
