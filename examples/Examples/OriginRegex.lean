import Keel.Regex

/-!
# Example: an origin allow-list, as `allow_origin_regex` uses it

starlette's `CORSMiddleware(allow_origin_regex=...)` accepts an origin when
`re.fullmatch(pattern, origin)` succeeds. Here the dialect is a small one:
literal characters, `.` (any character but `\n`) and ASCII ranges, which is
all a dialect has to supply (its atoms and its word characters); the matcher
and its laws come from `Keel.Regex`. The pattern is

    https://[a-z0-9-]+\.example\.org

The mode matters. `Mode.full` is `re.fullmatch`; under `Mode.search` (Rust's
`is_match`, Python's `re.search`) the same pattern also accepts an origin
that only contains an allowed one, `https://evil.com/?https://a.example.org`.

Inherits: `Regex.compile_test_iff` (the compiled pattern accepts exactly
`Accepts`), `Regex.accepts_full_iff` (in `Mode.full` that is `Matches` on the
whole origin), `Regex.reach_length_le` (no input makes it backtrack).
-/

namespace Examples.OriginRegex

open Keel Regex

/-- The dialect's atoms. -/
inductive Atom where
  | char (c : Char)
  | range (lo hi : Char)
  | dot
  deriving DecidableEq, Hashable, Repr

instance : CharClass Atom where
  test
    | .char a, c => c == a
    | .range lo hi, c => lo ≤ c && c ≤ hi
    | .dot, c => c != '\n'
  word c := c.isAlphanum || c == '_'

/-- A literal text. -/
def lit (s : String) : Regex Atom := s.toList.foldr (fun c r => .cat (.cls (.char c)) r) .eps

/-- One or more of a class. -/
def plus (k : Atom) : Regex Atom := .cat (.cls k) (.star (.cls k))

/-- A host label: `[a-z0-9-]+`. -/
def label : Regex Atom :=
  let k : Regex Atom := .alt (.cls (.range 'a' 'z')) (.alt (.cls (.range '0' '9')) (.cls (.char '-')))
  .cat k (.star k)

/-- `https://[a-z0-9-]+\.example\.org` -/
def pattern : Regex Atom := .cat (lit "https://") (.cat label (lit ".example.org"))

/-- `re.fullmatch`, compiled once. -/
def allowed : Matcher Atom := pattern.compile .full

/-- The same pattern as an unanchored search. -/
def contains : Matcher Atom := pattern.compile .search

/-- **An origin is allowed exactly when the whole of it matches the
pattern.** -/
theorem allowed_iff (origin : String) :
    allowed.test origin = true ↔ Matches pattern none origin.toList none := by
  rw [allowed, compile_test_iff, ← accepts_iff, accepts_full_iff]

theorem api_allowed : pattern.accepts .full "https://api.example.org".toList = true := by
  decide +kernel

theorem evil_refused :
    pattern.accepts .full "https://evil.com/?https://a.example.org".toList = false := by
  decide +kernel

/-- Under search the same text is accepted: the mode is part of the
contract, and `allow_origin_regex` needs `Mode.full`. -/
theorem evil_contains :
    pattern.accepts .search "https://evil.com/?https://a.example.org".toList = true := by
  decide +kernel

def run : IO Unit := do
  for o in ["https://api.example.org", "https://a-1.example.org", "http://api.example.org",
      "https://evil.com/?https://a.example.org", "https://api.example.org.evil.com"] do
    IO.println s!"{o}: fullmatch {allowed.test o}, search {contains.test o}"
  let long := "https://" ++ String.ofList (List.replicate 100000 'a') ++ ".example.org!"
  IO.println s!"a 100 000-character label with a bad tail: fullmatch {allowed.test long}"

end Examples.OriginRegex
