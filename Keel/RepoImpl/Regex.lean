import Keel.DataTypes.Regex

/-!
# Regular expressions: meaning and matching by partial derivatives

* `Matches r p u n`: `r` matches exactly the characters `u`, where `p` is
  the character before `u` and `n` the character after it (`none` at an end
  of the text). Classes and assertions read their characters with
  `CharClass.test` and `Assertion.holds`; the rest is the textbook language
  of a regular expression. A star's iterations are non-empty, which loses
  nothing: an empty iteration matches only where the star already matches.
* `Accepts m r t`: `r` matches a segment of `t` where the mode `m` allows it.
* `r.accepts m t` decides it. The scan reads `t` once, left to right,
  keeping a set of terms: Antimirov's partial derivatives of `r` by the text
  read so far, started at every position the mode allows, without
  duplicates. A term nullable at the next position is a match ending there.

There is no backtracking: every term of the set is `r` or one of its partial
derivatives `PD r`, at most one per character class of `r`
(`reach_length_le`), so the work per character is bounded by the pattern.
The scan is a tail loop over the text; the only other recursion is on the
pattern's terms. `RepoImpl/RegexNfa.lean` compiles the same scan to tables.
-/

namespace Keel

namespace Regex

variable {κ α : Type}

/-- Whether a character is in a class built from atoms. -/
def Cls.test [CharClass α] : Cls α → Char → Bool
  | .atom a, c => CharClass.test a c
  | .union k l, c => k.test c || l.test c
  | .inter k l, c => k.test c && l.test c
  | .diff k l, c => k.test c && !l.test c
  | .sym k l, c => k.test c != l.test c
  | .neg k, c => !k.test c

instance [CharClass α] : CharClass (Cls α) where
  test := Cls.test
  word := CharClass.word α

/-- Is the character next to a position a word character? None at the ends. -/
def wordAt (word : Char → Bool) : Option Char → Bool
  | some c => word c
  | none => false

/-- Whether an assertion holds between the character before (`p`) and the
character after (`n`); `none` is an end of the text. -/
def Assertion.holds (word : Char → Bool) : Assertion → Option Char → Option Char → Bool
  | .start, p, _ => p.isNone
  | .finish, _, n => n.isNone
  | .wordBoundary, p, n => wordAt word p != wordAt word n
  | .notWordBoundary, p, n => wordAt word p == wordAt word n
  | .wordStart, p, n => !wordAt word p && wordAt word n
  | .wordEnd, p, n => wordAt word p && !wordAt word n

end Regex

namespace Regex

variable {κ : Type} [CharClass κ]

/-! ## Meaning -/

/-- `r` matches `u`, between the characters `p` and `n`. -/
inductive Matches : Regex κ → Option Char → List Char → Option Char → Prop where
  | eps {p n} : Matches eps p [] n
  | cls {k c p n} : CharClass.test k c = true → Matches (cls k) p [c] n
  | assert {a p n} : a.holds (CharClass.word κ) p n = true → Matches (assert a) p [] n
  | altL {r s p u n} : Matches r p u n → Matches (alt r s) p u n
  | altR {r s p u n} : Matches s p u n → Matches (alt r s) p u n
  | cat {r s p u v n} : Matches r p u (v.head?.or n) → Matches s (u.getLast?.or p) v n →
      Matches (cat r s) p (u ++ v) n
  | starNil {r p n} : Matches (star r) p [] n
  | starCons {r p u v n} : u ≠ [] → Matches r p u (v.head?.or n) →
      Matches (star r) (u.getLast?.or p) v n → Matches (star r) p (u ++ v) n

/-- `r` matches a segment of `t` that the mode allows: `t = x ++ y` and
`x = u ++ v`, with `v` matched between the last character of `u` and the
first of `y`; `u` is empty when the start is anchored, `y` when the end is. -/
def Accepts (m : Mode) (r : Regex κ) (t : List Char) : Prop :=
  ∃ x y, t = x ++ y ∧ (m.anchorEnd = true → y = []) ∧
    ∃ u v, x = u ++ v ∧ (m.anchorStart = true → u = []) ∧ Matches r u.getLast? v y.head?

/-! ## Partial derivatives -/

/-- Whether `r` matches the empty string between `p` and `n`. -/
def nullable (p n : Option Char) : Regex κ → Bool
  | empty => false
  | eps => true
  | cls _ => false
  | assert a => a.holds (CharClass.word κ) p n
  | alt r s => nullable p n r || nullable p n s
  | cat r s => nullable p n r && nullable p n s
  | star _ => true

/-- Concatenation, dropping a leading `eps`. -/
@[specialize] def seq [DecidableEq κ] (r s : Regex κ) : Regex κ := if r = eps then s else cat r s

variable [DecidableEq κ]

/-- Partial derivatives of `r` by `c`, read just after the character `p`:
the terms that, matched after `c`, make up a match of `r` that starts
with `c`. -/
def pd (p : Option Char) (c : Char) : Regex κ → List (Regex κ)
  | empty => []
  | eps => []
  | cls k => if CharClass.test k c then [eps] else []
  | assert _ => []
  | alt r s => pd p c r ++ pd p c s
  | cat r s =>
    (pd p c r).map (seq · s) ++ (if nullable p (some c) r then pd p c s else [])
  | star r => (pd p c r).map (seq · (star r))

/-- Antimirov's partial derivatives of `r`, over every character. -/
def PD : Regex κ → List (Regex κ)
  | empty | eps | assert _ => []
  | cls _ => [eps]
  | alt r s => PD r ++ PD s
  | cat r s => (PD r).map (seq · s) ++ PD s
  | star r => (PD r).map (seq · (star r))

/-- The number of character classes in `r`. -/
def leaves : Regex κ → Nat
  | empty | eps | assert _ => 0
  | cls _ => 1
  | alt r s | cat r s => r.leaves + s.leaves
  | star r => r.leaves

/-- A state the scan for `r` can reach: no duplicates, and only `r` and its
partial derivatives. -/
def Reach (r : Regex κ) (T : List (Regex κ)) : Prop := T.Nodup ∧ ∀ q ∈ T, q ∈ r :: PD r

/-! ## The scan -/

/-- The list without duplicates (first occurrences kept, in reverse). -/
def uniq (l : List (Regex κ)) : List (Regex κ) := l.foldl (fun acc q => acc.insert q) []

/-- One step of the scan: the derivatives of the set by `c` read after `p`,
and, unless the start is anchored, `r` again for a match starting after `c`. -/
def next (m : Mode) (r : Regex κ) (p : Option Char) (c : Char) (T : List (Regex κ)) : List (Regex κ) :=
  let D := uniq (T.flatMap (pd p c))
  if m.anchorStart then D else D.insert r

/-- The scan, after the character `p`, on the rest of the text. Unless the
end is anchored, it stops at the first match. -/
def scan (m : Mode) (r : Regex κ) (p : Option Char) : List Char → List (Regex κ) → Bool
  | [], T => T.any (nullable p none)
  | c :: cs, T =>
    if !m.anchorEnd && T.any (nullable p (some c)) then true
    else scan m r (some c) cs (next m r p c T)

/-- **Whether `r` matches `t` where the mode allows** (`accepts_iff`). -/
def accepts (m : Mode) (r : Regex κ) (t : List Char) : Bool := scan m r none t [r]

end Regex

end Keel
