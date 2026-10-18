import Keel.DataTypes.Input

/-!
# The parser type

`Parser τ ε α` reads `τ` tokens and yields an `α` or fails with an `ε`. It runs
on any buffer `σ` with `Input σ τ`, at a position, and reports the position
after the value (or where it failed).

Two invariants are fields, so every parser has them and every combinator
proves them once:

* `run_eq`, *translation invariance*: running at position `i` of `s` is
  running at `0` on the tokens from `i` on, shifted by `i`. A parser cannot
  look behind its position, and its meaning is a function of a list.
* `pos_le`: a parser never reports a position past the end of its input.

Together they make the list semantics `Parser.parse : List τ → Reply τ ε α`
(in `RepoImpl/Parse.lean`) a complete description, so laws are stated on lists
while the code runs on arrays. They are also what totality needs: a loop
whose step reports a new position knows it is in bounds, so "the position
moved" is "fewer tokens remain", the measure of every well-founded recursion
in the library. There is no fuel.
-/

namespace Keel

/-- The outcome of running a parser on a buffer: a value and the position
after it, or an error and the position where it was detected. -/
inductive Result (ε α : Type) where
  | ok (a : α) (pos : Nat)
  | error (e : ε) (pos : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace Result

variable {ε α : Type}

/-- Move every position by `k`. -/
def shift (k : Nat) : Result ε α → Result ε α
  | ok a j => ok a (j + k)
  | error e j => error e (j + k)

/-- The position a result reports. -/
def pos : Result ε α → Nat
  | ok _ j => j
  | error _ j => j

/-- Transform the value of a success. -/
def map {β : Type} (f : α → β) : Result ε α → Result ε β
  | ok a j => ok (f a) j
  | error e j => error e j

@[simp] theorem map_ok {β : Type} (f : α → β) (a : α) (j : Nat) :
    (ok a j : Result ε α).map f = ok (f a) j := rfl
@[simp] theorem map_error {β : Type} (f : α → β) (e : ε) (j : Nat) :
    (error e j : Result ε α).map f = error e j := rfl
@[simp] theorem map_shift {β : Type} (f : α → β) (r : Result ε α) (k : Nat) :
    (r.shift k).map f = (r.map f).shift k := by cases r <;> rfl
@[simp] theorem pos_map {β : Type} (f : α → β) (r : Result ε α) : (r.map f).pos = r.pos := by
  cases r <;> rfl
theorem map_map {β γ : Type} (f : α → β) (g : β → γ) (r : Result ε α) :
    (r.map f).map g = r.map (g ∘ f) := by cases r <;> rfl

@[simp] theorem shift_ok (a : α) (j k : Nat) : (ok a j : Result ε α).shift k = ok a (j + k) := rfl
@[simp] theorem shift_error (e : ε) (j k : Nat) :
    (error e j : Result ε α).shift k = error e (j + k) := rfl
@[simp] theorem pos_ok (a : α) (j : Nat) : (ok a j : Result ε α).pos = j := rfl
@[simp] theorem pos_error (e : ε) (j : Nat) : (error e j : Result ε α).pos = j := rfl
@[simp] theorem shift_zero (r : Result ε α) : r.shift 0 = r := by cases r <;> rfl
theorem shift_shift (r : Result ε α) (a b : Nat) : (r.shift a).shift b = r.shift (a + b) := by
  cases r <;> simp [Nat.add_assoc]
@[simp] theorem pos_shift (r : Result ε α) (k : Nat) : (r.shift k).pos = r.pos + k := by
  cases r <;> rfl

end Result

/-- The outcome of a parser on a list: a value and the tokens left after it,
or an error and the tokens left where it was detected. This is the form every
law is stated in. -/
inductive Reply (τ ε α : Type) where
  | ok (a : α) (rest : List τ)
  | error (e : ε) (rest : List τ)
  deriving Repr, DecidableEq, Inhabited

namespace Reply

variable {τ ε α β : Type}

/-- Continue after a success. -/
def bind (r : Reply τ ε α) (k : α → List τ → Reply τ ε β) : Reply τ ε β :=
  match r with
  | ok a rest => k a rest
  | error e rest => error e rest

/-- Transform the value of a success. -/
def map (f : α → β) : Reply τ ε α → Reply τ ε β
  | ok a rest => ok (f a) rest
  | error e rest => error e rest

/-- The value, if the parse succeeded. -/
def value? : Reply τ ε α → Option α
  | ok a _ => some a
  | error _ _ => none

/-- The tokens left, either way. -/
def rest : Reply τ ε α → List τ
  | ok _ r => r
  | error _ r => r

@[simp] theorem bind_ok (a : α) (r : List τ) (k : α → List τ → Reply τ ε β) :
    (ok a r).bind k = k a r := rfl
@[simp] theorem bind_error (e : ε) (r : List τ) (k : α → List τ → Reply τ ε β) :
    (error e r : Reply τ ε α).bind k = error e r := rfl
@[simp] theorem map_ok (f : α → β) (a : α) (r : List τ) : (ok a r : Reply τ ε α).map f = ok (f a) r := rfl
@[simp] theorem map_error (f : α → β) (e : ε) (r : List τ) :
    (error e r : Reply τ ε α).map f = error e r := rfl

end Reply

/-- Read a result on a list: positions become the tokens left there. -/
def Result.toReply {τ ε α : Type} (l : List τ) : Result ε α → Reply τ ε α
  | .ok a j => .ok a (l.drop j)
  | .error e j => .error e (l.drop j)

@[simp] theorem Result.toReply_ok {τ ε α : Type} (l : List τ) (a : α) (j : Nat) :
    (Result.ok a j : Result ε α).toReply l = .ok a (l.drop j) := rfl
@[simp] theorem Result.toReply_error {τ ε α : Type} (l : List τ) (e : ε) (j : Nat) :
    (Result.error e j : Result ε α).toReply l = .error e (l.drop j) := rfl
theorem Result.toReply_shift {τ ε α : Type} (l : List τ) (r : Result ε α) (k : Nat) :
    (r.shift k).toReply l = r.toReply (l.drop k) := by
  cases r <;> simp [List.drop_drop, Nat.add_comm]
theorem Result.toReply_map {τ ε α β : Type} (l : List τ) (f : α → β) (r : Result ε α) :
    (r.map f).toReply l = (r.toReply l).map f := by
  cases r <;> rfl

/-- The errors the library's own primitives raise. A downstream error type
provides them (and adds its own kinds); `Keel.Parse.Error` is a ready-made
one. -/
class ParseError (ε : Type) where
  /-- A token was needed and the input ended. -/
  eof : ε
  /-- The next token is not one the parser accepts. -/
  unexpected : ε
  /-- A recursive parser (`Parser.fix`) called itself without consuming
  input; the grammar is left-recursive. -/
  stuck : ε

/-- A ready-made error type: the library's three kinds and a message. -/
inductive Parse.Error where
  | eof
  | unexpected
  | stuck
  | other (msg : String)
  deriving Repr, DecidableEq, Inhabited

instance : ParseError Parse.Error := ⟨.eof, .unexpected, .stuck⟩

instance : ParseError String :=
  ⟨"unexpected end of input", "unexpected token", "parser made no progress"⟩

instance : ParseError Unit := ⟨(), (), ()⟩

/-- A parser of `τ` tokens yielding `α`, failing with `ε`. The fields after
`run` are its invariants (see the module docstring). -/
structure Parser (τ ε α : Type) where
  /-- Run on a buffer at a position. -/
  run : {σ : Type} → [Input σ τ] → σ → Nat → Result ε α
  /-- Translation invariance: the result at position `i` is the result at `0`
  on the tokens from `i` on, shifted by `i`. -/
  run_eq : ∀ {σ : Type} [Input σ τ] (s : σ) (i : Nat),
    run s i = (run (Input.rest s i) 0).shift i
  /-- The position reported on a list is within it. -/
  pos_le : ∀ l : List τ, (run l 0).pos ≤ l.length

end Keel
