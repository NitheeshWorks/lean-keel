import Keel.Proofs.Parse

/-!
# APIs: running a parser

`Parser.runFrom` runs a parser on any buffer and returns, with a success, the
proof that it agrees with the parser's list meaning. `Parser.parseAll`
requires the whole input to be consumed. `parseBytes` and `parseString` are
the two everyday entry points.
-/

namespace Keel

namespace Parser

variable {σ τ ε α : Type} [Input σ τ]

/-- Run `p` on `s` from position `i`: the value and the position after it, or
the error and where it was detected. A success says what it means: the
parser's list meaning on the tokens from `i` gives the same value and leaves
exactly the tokens from the reported position. -/
def runFrom (p : Parser τ ε α) (s : σ) (i : Nat := 0) :
    Except (ε × Nat) {r : α × Nat // p.parse (Input.rest s i) = .ok r.1 (Input.rest s r.2)} :=
  match h : p.run s i with
  | .ok a j => .ok ⟨(a, j), p.parse_of_run h⟩
  | .error e j => .error (e, j)

/-- `p` followed by the end of input succeeds exactly when `p` consumes all. -/
theorem parse_seqLeft_eof [ParseError ε] (p : Parser τ ε α) (l : List τ) (a : α) (r : List τ) :
    (p <* eof).parse l = .ok a r ↔ p.parse l = .ok a [] ∧ r = [] := by
  rw [parse_seqLeft]
  cases p.parse l with
  | ok b r' =>
    cases r' with
    | nil => simp
    | cons t r' => simp
  | error e r' => simp

/-- Parse the whole buffer: a success is a value `a` with
`p.parse (Input.toList s) = .ok a []`, all input consumed. A failure is the
error and its position (including `unexpected` at the first token `p` left
unread). -/
def parseAll [ParseError ε] (p : Parser τ ε α) (s : σ) :
    Except (ε × Nat) {a : α // p.parse (Input.toList s) = .ok a []} :=
  match (p <* eof).runFrom s 0 with
  | .ok ⟨(a, _), h⟩ => .ok ⟨a, ((parse_seqLeft_eof p _ a _).1 (by simpa using h)).1⟩
  | .error e => .error e

/-- Parse a whole byte string. -/
def parseBytes [ParseError ε] (p : Parser UInt8 ε α) (b : ByteArray) :
    Except (ε × Nat) {a : α // p.parse b.data.toList = .ok a []} :=
  p.parseAll b

/-- Parse a whole string, as characters. Positions are character indices. -/
def parseString [ParseError ε] (p : Parser Char ε α) (s : String) :
    Except (ε × Nat) {a : α // p.parse s.toList = .ok a []} :=
  match p.parseAll s.toList.toArray with
  | .ok ⟨a, h⟩ => .ok ⟨a, by simpa [Input.toList] using h⟩
  | .error e => .error e

end Parser

end Keel
