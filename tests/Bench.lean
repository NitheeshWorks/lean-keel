import Keel

/-!
# Bench: routing time on long request paths

Native timings, with a bound per case, for what an attacker controls: the
request path. Each case is a template and a path of 65535 characters (or
1 MiB of digits), and the bound is well under what a server would tolerate;
matching is linear in the path, so the measured times are a small fraction of
the bounds. The run also checks the expected outcome, so a fast wrong answer
fails too.

Run with `lake exe bench`. Exits non-zero when a case is wrong or over its
bound. The sizes are read at run time (`lake exe bench <scale>` multiplies
them), so nothing is evaluated at compile time.
-/

open Keel

/-- A path of `n` characters: `pre`, then `fill` repeated, then `post`. -/
def mkPath (pre : String) (fill : Char) (post : String) (n : Nat) : String :=
  pre ++ String.ofList (List.replicate (n - pre.length - post.length) fill) ++ post

structure Case where
  name : String
  template : String
  path : String
  expect : Bool
  boundMs : Nat

def cases (scale : Nat) : List Case :=
  let n := 65535 * scale
  let mib := 1048576 * scale
  [ ⟨"str, no match", "/s/{a}/x", mkPath "/s/" 'a' "" n, false, 100⟩,
    ⟨"str, match", "/s/{a}/x", mkPath "/s/" 'a' "/x" n, true, 100⟩,
    ⟨"path, no match", "/p/{a:path}/end", mkPath "/p/" 'a' "" n, false, 100⟩,
    ⟨"path, match", "/p/{a:path}/end", mkPath "/p/" 'a' "/end" n, true, 100⟩,
    ⟨"path of slashes, no match", "/p/{a:path}/end", mkPath "/p/" '/' "" n, false, 100⟩,
    ⟨"two str, no match", "/u/{a}-{b}", mkPath "/u/" 'a' "" n, false, 100⟩,
    ⟨"two str, match", "/u/{a}-{b}", mkPath "/u/" 'a' "-b" n, true, 100⟩,
    ⟨"int, no match", "/i/{n:int}/x", mkPath "/i/" '7' "" n, false, 100⟩,
    ⟨"int, 1 MiB of digits", "/i/{n:int}", mkPath "/i/" '7' "" mib, false, 100⟩,
    ⟨"int, 4300 digits", "/i/{n:int}", mkPath "/i/" '7' "" (4303 * scale), scale == 1, 100⟩,
    ⟨"int, 4301 digits", "/i/{n:int}", mkPath "/i/" '7' "" (4304 * scale), false, 100⟩,
    ⟨"float, no match", "/f/{x:float}/x", mkPath "/f/" '7' "" n, false, 100⟩,
    ⟨"float, 1 MiB of digits", "/f/{x:float}", mkPath "/f/" '7' "" mib, true, 1000⟩,
    ⟨"uuid, no match", "/d/{u:uuid}/x", mkPath "/d/" 'a' "" n, false, 100⟩ ]

def timeMs {α : Type} (f : Unit → α) (use : α → Bool) : IO (Bool × Nat) := do
  let t0 ← IO.monoNanosNow
  let r := use (f ())
  -- force `r` before reading the clock again
  if r then pure () else pure ()
  let t1 ← IO.monoNanosNow
  pure (r, (t1 - t0) / 1000000)

/-! ## Compiling patterns with context assertions

The bench family lean-pydantic ships, `(\b[a-z]{1,30}\b\s?){1,20}`, under
`^ $`, `(?m)`, `(?mR)`, with an ASCII `\b` and half boundaries (critic-1's
rows on z5puu6tl9gaw). A pattern with the new assertions may compile at most
twice as long as the same pattern with the old `^`, `$`, `\b` (the `base`
row), and each row has an absolute bound. -/

/-- A small Rust-like dialect: ranges, `\s`, `\w`, `.`. -/
inductive Atom where
  | range (lo hi : Char)
  | space
  | word
  | dot
  deriving DecidableEq, Hashable, Repr

def isW (c : Char) : Bool := c.isAlphanum || c == '_' || (c.toNat ≥ 0xC0 && c.toNat ≠ 0xD7 && c.toNat ≠ 0xF7)

instance : CharClass Atom where
  test
    | .range lo hi, c => lo ≤ c && c ≤ hi
    | .space, c => c == ' ' || c == '\t' || c == '\n' || c == '\r'
    | .word, c => isW c
    | .dot, c => c != '\n'
  word := isW

open Regex in
section
abbrev R := Regex Atom
def opt (r : R) : R := .alt r .eps
def rep (r : R) : Nat → R
  | 0 => .eps
  | n + 1 => .cat r (rep r n)
/-- `r` at most `n` times, nested as lean-pydantic lowers it: `(r(r…)?)?`. -/
def upto (r : R) : Nat → R
  | 0 => .eps
  | n + 1 => .alt (.cat r (upto r n)) .eps
/-- `r{lo,hi}` -/
def counted (r : R) (lo hi : Nat) : R := .cat (rep r lo) (upto r (hi - lo))
def a (x : Assertion) : R := .assert x
def seqR : List R → R := List.foldr .cat .eps
def az : R := .cls (.range 'a' 'z')
/-- `(\<pre>[a-z]{1,30}<post>\s?){1,20}` between `start` and `finish`. -/
def family (start finish : List R) (pre post : List R) : R :=
  seqR (start ++ [counted (seqR (pre ++ [counted az 1 30] ++ post ++ [opt (.cls .space)])) 1 20] ++ finish)
end

open Regex.Assertion in
def compileRows : List (String × Regex Atom) :=
  [ ("base: ^(\\b[a-z]{1,30}\\b\\s?){1,20}$",
      family [a start] [a finish] [a wordBoundary] [a wordBoundary]),
    ("(?m)^(\\b[a-z]{1,30}\\b\\s?){1,20}$",
      family [a lineStart] [a lineEnd] [a wordBoundary] [a wordBoundary]),
    ("(?mR)^(\\b[a-z]{1,30}\\b\\s?){1,20}$",
      family [a lineStartCRLF] [a lineEndCRLF] [a wordBoundary] [a wordBoundary]),
    ("(?mR)^(\\b[a-z]{1,30}(?-u:\\b)\\s?){1,20}$\\b{start-half}",
      family [a lineStartCRLF] [a lineEndCRLF, a wordStartHalf] [a wordBoundary] [a wordBoundaryAscii]),
    ("(?mR)^(\\b{start-half}[a-z]{1,30}\\b{end-half}(?-u:\\b)\\s?){1,20}$",
      family [a lineStartCRLF] [a lineEndCRLF] [a wordStartHalf] [a wordEndHalf, a wordBoundaryAscii]),
    ("(?m)^\\w+\\b.*$\\b{start-half}",
      seqR [a lineStart, .cls .word, .star (.cls .word), a wordBoundary, .star (.cls .dot), a lineEnd, a wordStartHalf]) ]

/-- Time `Nfa.build` on a pattern read from a reference (so nothing is
compiled ahead of the clock). -/
def buildMs (r : Regex Atom) : IO (Bool × Nat) := do
  let ref ← IO.mkRef r
  let r ← ref.get
  timeMs (fun () => Regex.Nfa.build r) Option.isSome

def main (args : List String) : IO UInt32 := do
  let scale := (args.head? >>= String.toNat?).getD 1
  let mut bad := 0
  for c in cases scale do
    let _ := c.path.length  -- build the path outside the timed region
    match PathTemplate.compile c.template with
    | .error e => IO.println s!"FAIL {c.name}: {e}"; bad := bad + 1
    | .ok t =>
      let (r, ms) ← timeMs (fun () => t.match c.path) Option.isSome
      let ok := r == c.expect && ms ≤ c.boundMs
      IO.println s!"{if ok then "ok  " else "FAIL"} {c.name}: {ms} ms (bound {c.boundMs}), matched {r}"
      unless ok do bad := bad + 1
  -- rendering and reading long decimals
  let big := 10 ^ (65535 * scale) + 1
  let (ok, ms) ← timeMs (fun () => Codec.decimal big) (fun d => d.length == 65536 * scale)
  IO.println s!"{if ok && ms ≤ 1000 then "ok  " else "FAIL"} decimal of a 65536-digit number: {ms} ms (bound 1000)"
  unless ok && ms ≤ 1000 do bad := bad + 1
  let digits := List.replicate (1048576 * scale) '7'
  let _ := digits.length
  let (ok, ms) ← timeMs (fun () => Codec.digitsValue digits) (fun v => v % 10 == 7)
  IO.println s!"{if ok && ms ≤ 1000 then "ok  " else "FAIL"} digitsValue of 1 MiB of digits: {ms} ms (bound 1000)"
  unless ok && ms ≤ 1000 do bad := bad + 1
  -- compiling patterns with context assertions: each within 2x the base row, and under 1 s
  let mut baseMs := 0
  for (name, r) in compileRows do
    let (built, ms) ← buildMs r
    if baseMs == 0 then baseMs := max ms 1
    let bound := min 1000 (2 * baseMs + 20)
    let ok := built && ms ≤ bound
    IO.println s!"{if ok then "ok  " else "FAIL"} compile {name}: {ms} ms (bound {bound}), tables built {built}"
    unless ok do bad := bad + 1
  if bad == 0 then IO.println "bench: all within bounds"; pure 0
  else IO.println s!"bench: {bad} failing"; pure 1
