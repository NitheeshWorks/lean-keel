import Keel.APIs.Regex

/-!
# Specifications: regular expressions

The headline laws of `Keel.Regex`, proved in `Proofs/Regex.lean` and
`APIs/Regex.lean`, with slots in `Proofs/Verified.lean`. Each holds for any
character classes `κ`.
-/

namespace Keel.Spec

open Regex

/-- `nullable` decides the empty match in context. -/
def RegexNullable : Prop :=
  ∀ (κ : Type) [CharClass κ] (r : Regex κ) (p n : Option Char),
    nullable p n r = true ↔ Matches r p [] n

/-- Antimirov's theorem, in context: the partial derivatives by `c` are the
ways to finish a match that starts with `c`. -/
def RegexDeriveCorrect : Prop :=
  ∀ (κ : Type) [CharClass κ] [DecidableEq κ] (p : Option Char) (c : Char) (r : Regex κ)
    (u : List Char) (n : Option Char),
    Matches r p (c :: u) n ↔ ∃ q ∈ pd p c r, Matches q (some c) u n

/-- The scan decides acceptance, in every mode. -/
def RegexAcceptsIff : Prop :=
  ∀ (κ : Type) [CharClass κ] [DecidableEq κ] (m : Mode) (r : Regex κ) (t : List Char),
    r.accepts m t = true ↔ Accepts m r t

/-- The compiled matcher is the scan. -/
def RegexCompiledEq : Prop :=
  ∀ (κ : Type) [CharClass κ] [DecidableEq κ] (r : Regex κ) (N : Nfa r) (m : Mode) (t : List Char),
    N.accepts m t = r.accepts m t

/-- The scan's state is bounded by the pattern. -/
def RegexStateBound : Prop :=
  ∀ (κ : Type) [CharClass κ] [DecidableEq κ] (r : Regex κ) (T : List (Regex κ)),
    Reach r T → T.length ≤ r.leaves + 1

/-- Every step keeps the state reachable. -/
def RegexReachNext : Prop :=
  ∀ (κ : Type) [CharClass κ] [DecidableEq κ] (m : Mode) (r : Regex κ) (T : List (Regex κ))
    (p : Option Char) (c : Char), Reach r T → Reach r (next m r p c T)

/-- A compiled pattern accepts exactly what the mode allows `r` to match. -/
def RegexCompileTest : Prop :=
  ∀ (κ : Type) [CharClass κ] [DecidableEq κ] [Hashable κ] (r : Regex κ) (m : Mode) (s : String),
    (r.compile m).test s = true ↔ Accepts m r s.toList

end Keel.Spec
