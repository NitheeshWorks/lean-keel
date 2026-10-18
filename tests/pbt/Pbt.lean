import Keel
import Plausible

/-!
# Plausible properties

Randomised checks run at build time with `plausible` (`#eval
Testable.check`, which fails the build on a counter-example). Each restates a
proved law on plausible's own generators, as a smoke test of the definitions
the theorems are about, run on the executable buffers (`ByteArray`,
`String`) rather than the lists the proofs use.
-/

namespace Pbt

open Keel

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

-- Codec.nat: decimal round trip before a non-digit (Codec.nat_lawful).
#eval Plausible.Testable.check (∀ n : Nat,
    Codec.nat.decodeString (Codec.nat.encodeString n ++ ",") = some (n, ","))

-- Codec.natBE on bytes, any continuation (Codec.natBE_lawful).
#eval Plausible.Testable.check (∀ (n : Nat) (rest : List UInt8),
    ((Codec.natBE 4).decodeBytes ((Codec.natBE 4).encodeBytes (n % 2 ^ 32) ++ bytes rest)).map
      (fun (a, r) => (a, r.data.toList)) = some (n % 2 ^ 32, rest))

-- Codec.lengthPrefixed (Codec.lengthPrefixed_lawful).
#eval Plausible.Testable.check (∀ (l rest : List UInt8),
    let c := Codec.lengthPrefixed (Codec.natBE 2) (Codec.rest : Codec UInt8 (List UInt8))
    c.decode (c.encode (l.take 1000) ++ rest) = some (l.take 1000, rest))

-- Codec.delimited with a CR-free value (Codec.delimited_lawful).
#eval Plausible.Testable.check (∀ (l rest : List UInt8),
    let v := l.filter (· != 13)
    (Codec.delimited [13, 10] (Codec.rest : Codec UInt8 (List UInt8))).decode (v ++ [13, 10] ++ rest) =
      some (v, rest))

-- Parse.takeWhile on a ByteArray is List.takeWhile (parse_takeWhile, run_eq_of_parse).
#eval Plausible.Testable.check (∀ l : List UInt8,
    (match (Parser.takeWhile (· < 100) : Parser UInt8 Parse.Error (List UInt8)).runFrom (bytes l) 0 with
     | .ok ⟨(v, _), _⟩ => v
     | .error _ => []) = l.takeWhile (· < 100))

-- Refine.validate_iff on integers.
#eval Plausible.Testable.check (∀ (x lo hi : Int),
    let c : Constraint Int := .and (.ge lo) (.le hi)
    (c.validate x matches .ok _) = decide (lo ≤ x ∧ x ≤ hi))

-- Route.match_urlFor for an int capture.
#eval Plausible.Testable.check (∀ n : Nat,
    (path% "/items/{item_id:int}").match ((path% "/items/{item_id:int}").urlFor (n, ())) = some (n, ()))

end Pbt
