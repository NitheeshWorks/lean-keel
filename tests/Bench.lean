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
  if bad == 0 then IO.println "bench: all within bounds"; pure 0
  else IO.println s!"bench: {bad} failing"; pure 1
