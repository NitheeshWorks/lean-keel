import Keel.Refine
import Lean.Elab.Term

/-!
# Keel.Refine.Elab: refined literals

The one part of `Keel.Refine` that needs Lean's elaborator: a numeral or
string literal where a refined value is expected checks its constraint by
`decide`, so `(discount : Nat ∣ le 100 := 0)` and `greet "anon"` elaborate.

It is a separate module because importing Lean's elaborator roughly doubles
the memory of every module that imports it. The definitions, theorems and the
`α ∣ c` notation are in `Keel.Refine`, which imports only Init; `import Keel`
brings this module too. A module that only defines or proves things imports
`Keel.Refine`; one that writes refined literals imports `Keel.Refine.Elab`
(or `Keel`).
-/

namespace Keel

open Lean Elab Term in
/-- A literal where a refined value is expected checks its constraint by
`decide`. Declines (leaving the literal to Lean's own elaborator) unless the
expected type is known to be `Refined α c`. -/
def elabRefinedLit : TermElab := fun stx expectedType? => do
  let some ty := expectedType? | throwUnsupportedSyntax
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``Refined 2 do throwUnsupportedSyntax
  elabTerm (← `(Subtype.mk $(⟨stx⟩) (by decide))) ty

/-- Numerals: `(discount : Nat ∣ le 100 := 0)`, `pct 50`. -/
@[term_elab num] def elabRefinedNum : Lean.Elab.Term.TermElab := elabRefinedLit

/-- String literals: `(name : String ∣ minLength 1 := "anon")`. -/
@[term_elab str] def elabRefinedStr : Lean.Elab.Term.TermElab := elabRefinedLit

end Keel
