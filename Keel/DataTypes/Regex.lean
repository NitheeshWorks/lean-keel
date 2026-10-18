/-!
# Regular expressions: terms, classes, assertions, modes

The terms a dialect's parser compiles a pattern to. Keel's matcher works on
them by partial derivatives (`RepoImpl/Regex.lean`), with no backtracking.
Each dialect keeps only its parser: pydantic-core's Rust `regex` dialect,
Python's `re` for starlette's `allow_origin_regex`, and so on.

* **Character classes** are a parameter `κ`, read through `CharClass κ`: a
  dialect gives its own atoms (`\d` with its Unicode tables, `.` with or
  without `\n`) and its notion of a word character, which the word
  assertions read. `Regex.Cls α` closes any atoms under union, intersection,
  difference, symmetric difference and negation.
* **Zero-width assertions** (`^`, `$`, `\b`, …) are terms: the text's ends,
  line ends (`\n`, or `\r\n` taken as one break), and word boundaries over
  the dialect's word characters or ASCII ones, whole or half. Whether one
  holds depends only on the characters on either side of the position, so
  the semantics carries the character before and the character after each
  matched segment.
* **The mode** says where a match may start and end: anywhere (Rust's
  `is_match`, Python's `re.search`), at the start (`re.match`), or the whole
  text (`re.fullmatch`).
-/

namespace Keel

/-- How a dialect reads its character classes: membership, and which
characters are word characters (for `\b` and its kin). -/
class CharClass (κ : Type) where
  /-- Whether a character is in the class. -/
  test : κ → Char → Bool
  /-- Whether a character is a word character (`\w`), for the word
  assertions. -/
  word : Char → Bool

namespace Regex

/-- A character class built from atoms `α`: Rust's class operations. -/
inductive Cls (α : Type) where
  | atom (a : α)
  /-- `[ab]` -/
  | union (k l : Cls α)
  /-- `[a&&b]` -/
  | inter (k l : Cls α)
  /-- `[a--b]` -/
  | diff (k l : Cls α)
  /-- `[a~~b]` -/
  | sym (k l : Cls α)
  /-- `[^a]` -/
  | neg (k : Cls α)
  deriving DecidableEq, Hashable, Repr

/-- A zero-width assertion. -/
inductive Assertion where
  /-- `^`, `\A`: the start of the text. -/
  | start
  /-- `\z` (and Rust's `$`): the end of the text. -/
  | finish
  /-- `\b` -/
  | wordBoundary
  /-- `\B` -/
  | notWordBoundary
  /-- `\<` -/
  | wordStart
  /-- `\>` -/
  | wordEnd
  /-- `(?m)^`: the start of the text or of a line (after `\n`). -/
  | lineStart
  /-- `(?m)$`: the end of the text or of a line (before `\n`). -/
  | lineEnd
  /-- `(?mR)^`: the start of the text or of a line, after `\n` or after a
  `\r` not followed by `\n` (never between the `\r` and `\n` of `\r\n`). -/
  | lineStartCRLF
  /-- `(?mR)$`: the end of the text or of a line, before `\r` or before a
  `\n` not preceded by `\r` (never between the `\r` and `\n` of `\r\n`). -/
  | lineEndCRLF
  /-- `(?-u:\b)`: `\b` over the ASCII word characters `[0-9A-Za-z_]`. -/
  | wordBoundaryAscii
  /-- `(?-u:\B)` -/
  | notWordBoundaryAscii
  /-- `(?-u:\<)` -/
  | wordStartAscii
  /-- `(?-u:\>)` -/
  | wordEndAscii
  /-- `\b{start-half}`: no word character before (whatever follows). -/
  | wordStartHalf
  /-- `\b{end-half}`: no word character after (whatever precedes). -/
  | wordEndHalf
  /-- `(?-u:\b{start-half})` -/
  | wordStartHalfAscii
  /-- `(?-u:\b{end-half})` -/
  | wordEndHalfAscii
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Where a match may lie in the text. -/
structure Mode where
  /-- The match starts at the start of the text. -/
  anchorStart : Bool := false
  /-- The match ends at the end of the text. -/
  anchorEnd : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Anywhere in the text: Rust's `Regex::is_match`, Python's `re.search`. -/
def Mode.search : Mode := {}

/-- At the start of the text: Python's `re.match`. -/
def Mode.prefix : Mode := { anchorStart := true }

/-- The whole text: Python's `re.fullmatch`. -/
def Mode.full : Mode := { anchorStart := true, anchorEnd := true }

end Regex

/-- A regular expression over character classes `κ`. -/
inductive Regex (κ : Type) where
  /-- Matches nothing. -/
  | empty
  /-- Matches the empty string. -/
  | eps
  /-- One character of a class. -/
  | cls (k : κ)
  /-- The empty string, where the assertion holds. -/
  | assert (a : Regex.Assertion)
  | alt (r s : Regex κ)
  | cat (r s : Regex κ)
  | star (r : Regex κ)
  deriving DecidableEq, Hashable, Repr

instance {κ : Type} : Inhabited (Regex κ) := ⟨.empty⟩

end Keel
