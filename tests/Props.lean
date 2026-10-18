import Keel

/-!
# Property tests: fast feedback where there is no proof

Every law here is also a theorem; these properties exercise the *running*
code on random inputs, on `ByteArray`, `Array` and `String` buffers, which
the theorems reach through `Parser.run_eq_of_parse`. A property failing here
while its theorem holds would mean the definitions are not what the
statements say. Each combinator has at least one property.

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

open Keel

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

/-- A list of `n` values drawn by `g`. -/
def Rng.list {α : Type} (r : Rng) (n : Nat) (g : Rng → α × Rng) : List α × Rng :=
  match n with
  | 0 => ([], r)
  | n + 1 =>
    let (x, r) := g r
    let (xs, r) := r.list n g
    (x :: xs, r)

def Rng.byte (r : Rng) : UInt8 × Rng := let (n, r) := r.nat 256; (n.toUInt8, r)

def Rng.bytes (r : Rng) (max : Nat) : List UInt8 × Rng :=
  let (n, r) := r.nat (max + 1)
  r.list n Rng.byte

/-- A byte other than CR. -/
def Rng.lineByte (r : Rng) : UInt8 × Rng := let (n, r) := r.nat 255; ((if n ≥ 13 then n + 1 else n).toUInt8, r)

def Rng.char (r : Rng) (alphabet : List Char) : Char × Rng :=
  let (n, r) := r.nat alphabet.length
  (alphabet.getD n 'a', r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng
  /-- How many random cases; a fixed native probe runs once. -/
  cases : Nat := 200

def prop {α : Type} (name : String) (gen : Rng → α × Rng) (ok : α → Bool) (display : α → String) : Property :=
  { name, check := fun r => let (a, r) := gen r; (if ok a then none else some (display a), r) }

/-- A fixed check on a large input, run once (a native resource probe). -/
def probe (name : String) (ok : Unit → Bool) (what : String) : Property :=
  { name, check := fun r => (if ok () then none else some what, r), cases := 1 }

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-! ## Generators of structured values -/

inductive Tree where
  | leaf (n : Nat)
  | node (ts : List Tree)

def Tree.render : Tree → List Char
  | .leaf n => Codec.decimal n
  | .node ts => '[' :: (renderList ts) ++ [']']
where renderList : List Tree → List Char
  | [] => []
  | [t] => t.render
  | t :: ts => t.render ++ ',' :: renderList ts

def Tree.beq : Tree → Tree → Bool
  | .leaf a, .leaf b => a == b
  | .node as, .node bs => beqList as bs
  | _, _ => false
where beqList : List Tree → List Tree → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && beqList as bs
  | _, _ => false

def Rng.tree (r : Rng) : Nat → Tree × Rng
  | 0 => let (n, r) := r.nat 1000; (.leaf n, r)
  | d + 1 =>
    let (k, r) := r.nat 3
    if k == 0 then let (n, r) := r.nat 1000; (.leaf n, r)
    else
      let (n, r) := r.nat 4
      let (ts, r) := r.list n (fun r => r.tree d)
      (.node ts, r)

open Parser in
/-- One level of the bracket grammar. -/
def treeBody (self : Parser Char Parse.Error Tree) : Parser Char Parse.Error Tree :=
  (do let ds ← many1 (satisfy Char.isDigit); pure (.leaf (Codec.digitsValue ds)))
  <|> (do let _ ← token '['; let ts ← sepBy self (token ','); let _ ← token ']'; pure (.node ts))

open Parser in
def treeP : Parser Char Parse.Error Tree := fixDepth 512 treeBody

/-! ## Codecs under test -/

-- Helper: string literal as bytes.
def crlf : List UInt8 := [13, 10]

def lines : Codec UInt8 ByteArray := Codec.delimited crlf Codec.bytes
def headerBlock : Codec UInt8 (List ByteArray) := lines.many
def framed : Codec UInt8 ByteArray := Codec.lengthPrefixed (Codec.natBE 2) Codec.bytes
def framedList : Codec UInt8 (List ByteArray) := framed.manyTill [0, 0]
def pairCodec : Codec UInt8 (Nat × Nat) := (Codec.natBE 1).seq (Codec.natBE 4)
def sumCodec : Codec UInt8 (Nat ⊕ ByteArray) := Codec.sum [1] [2] (Codec.natBE 2) framed
def evenCodec : Codec UInt8 {n : Nat // n % 2 = 0} := (Codec.natBE 2).refine fun n => n % 2 = 0
def doubled : Codec UInt8 Nat := (Codec.natBE 1).map (· / 2) (· * 2) (by intro n; show n * 2 / 2 = n; omega)
def tagged : Codec UInt8 (Σ _ : Nat, Nat) := Codec.sigma (Codec.natBE 1) fun t => Codec.natBE (t % 4 + 1)
def csv : Codec Char (Nat × Nat) := (Codec.nat.left (Codec.lit [','])).seq Codec.nat

def roundTrip {α : Type} (c : Codec UInt8 α) (a : α) (rest : List UInt8) (eq : α → α → Bool) : Bool :=
  match c.decodeBytes (c.encodeBytes a ++ bytes rest) with
  | some (a', r) => eq a a' && r.data.toList == rest
  | none => false

/-- `n` nested brackets. -/
def nestedBrackets (n : Nat) : Array Char := (List.replicate n '[' ++ List.replicate n ']').toArray

def properties : List Property := [
  probe "Parse.fixDepth: 10^6 nested brackets fail with depthExceeded, natively, no crash"
    (fun _ => match treeP.runFrom (nestedBrackets 1000000) 0 with
      | .error (.depthExceeded, _) => true
      | _ => false)
    "nesting 10^6",
  prop "Parse.fixDepth_ok: a shallow bound, when it succeeds, gives fix's result"
    (fun r => r.tree 4)
    (fun t => let s := t.render
      match (Parser.fixDepth 2 treeBody).parse s with
      | .ok a [] => match (Parser.fix treeBody).parse s with
        | .ok b [] => a.beq b
        | _ => false
      | .ok _ _ => false
      | .error _ _ => true)
    (fun t => String.ofList t.render),
  prop "Parse.fixDepth agrees with fix within the bound"
    (fun r => r.tree 4)
    (fun t => let s := t.render
      (treeP.parse s matches .ok _ []) &&
        match (treeP.parse s), ((Parser.fix fun self => treeBody self).parse s) with
        | .ok a [], .ok b [] => a.beq b
        | _, _ => false)
    (fun t => String.ofList t.render),
  probe "Parse.takeWhile runs in constant stack on 10^7 bytes"
    (fun _ =>
      let bs : ByteArray := ⟨Array.replicate 10000000 97⟩
      match (Parser.takeWhile (· == 97) : Parser UInt8 Parse.Error _).runFrom bs 0 with
      | .ok ⟨(v, j), _⟩ => v.length == 10000000 && j == 10000000
      | .error _ => false)
    "width 10^7",
  -- Parse
  prop "Parse.takeWhile is List.takeWhile, on a ByteArray"
    (fun r => r.bytes 40)
    (fun l => match (Parser.takeWhile (· < 128) : Parser UInt8 Parse.Error _).runFrom (bytes l) 0 with
      | .ok ⟨(v, j), _⟩ => v == l.takeWhile (· < 128) && j == (l.takeWhile (· < 128)).length
      | .error _ => false)
    toString,
  prop "Parse.many and sepBy read a comma list, on an Array"
    (fun r => r.list 6 (fun r => r.nat 100000))
    (fun ns =>
      let text := (",".intercalate (ns.map toString)).toList.toArray
      match (Parser.sepBy (Parser.many1 (Parser.satisfy Char.isDigit)) (Parser.token ',') :
          Parser Char Parse.Error _).runFrom text 0 with
      | .ok ⟨(v, _), _⟩ => v.map Codec.digitsValue == ns
      | .error _ => false)
    toString,
  prop "Parse.fix reads nested brackets"
    (fun r => r.tree 4)
    (fun t => match treeP.parseString (String.ofList t.render) with
      | .ok ⟨v, _⟩ => v.beq t
      | .error _ => false)
    (fun t => String.ofList t.render),
  prop "Parse.lit and startsWith agree with the prefix relation"
    (fun r => let (a, r) := r.bytes 3; let (b, r) := r.bytes 5; ((a, b), r))
    (fun (a, b) => match (Parser.startsWith a : Parser UInt8 Parse.Error Bool).runFrom (bytes b) 0 with
      | .ok ⟨(v, j), _⟩ => v == decide (a <+: b) && j == 0
      | .error _ => false)
    toString,
  prop "Parse.isolate confines a parser to n tokens"
    (fun r => let (l, r) := r.bytes 20; let (n, r) := r.nat 25; ((l, n), r))
    (fun (l, n) => match (Parser.isolate n (Parser.takeWhile fun _ => true) :
        Parser UInt8 Parse.Error (List UInt8)).runFrom (bytes l) 0 with
      | .ok ⟨(v, j), _⟩ => n ≤ l.length && v == l.take n && j == n
      | .error _ => l.length < n)
    toString,
  -- Codec
  prop "Codec.natBE round-trips on any continuation"
    (fun r => let (w, r) := r.nat 5; let (n, r) := r.nat (256 ^ w); let (rest, r) := r.bytes 8; ((w, n, rest), r))
    (fun (w, n, rest) => roundTrip (Codec.natBE w) n rest (· == ·))
    toString,
  prop "Codec.nat round-trips before a non-digit"
    (fun r => let (n, r) := r.nat 1000000000; let (c, r) := r.char ['x', ',', ' ', '.']; ((n, c), r))
    (fun (n, c) => Codec.nat.decodeString (Codec.nat.encodeString n ++ String.singleton c) ==
      some (n, String.singleton c))
    toString,
  prop "Codec.seq / left / lit round-trip (csv pair)"
    (fun r => let (a, r) := r.nat 100000; let (b, r) := r.nat 100000; ((a, b), r))
    (fun p => csv.decodeString (csv.encodeString p ++ ";") == some (p, ";"))
    toString,
  prop "Codec.seq of fixed widths round-trips"
    (fun r => let (a, r) := r.nat 256; let (b, r) := r.nat (2 ^ 32); let (rest, r) := r.bytes 6; ((a, b, rest), r))
    (fun (a, b, rest) => roundTrip pairCodec (a, b) rest (· == ·))
    toString,
  prop "Codec.delimited + many: header lines round-trip"
    (fun r => r.list 5 (fun r => let (n, r) := r.nat 20; let (l, r) := r.list n Rng.lineByte; (bytes l, r)))
    (fun ls => match headerBlock.decodeBytes (headerBlock.encodeBytes ls) with
      | some (ls', r) => ls'.map (·.data.toList) == ls.map (·.data.toList) && r.size == 0
      | none => false)
    (fun ls => toString (ls.map (·.data.toList))),
  prop "Codec.lengthPrefixed + manyTill: frames round-trip on any continuation"
    (fun r => let (fs, r) := r.list 4 (fun r => let (l, r) := r.bytes 30; (bytes (l.filter (· != 0) ++ [1]), r))
      let (rest, r) := r.bytes 5; ((fs, rest), r))
    (fun (fs, rest) => roundTrip framedList fs rest fun a b => a.map (·.data.toList) == b.map (·.data.toList))
    (fun (fs, rest) => toString (fs.map (·.data.toList), rest)),
  prop "Codec.sum round-trips both sides"
    (fun r => let (k, r) := r.nat 2; let (n, r) := r.nat 65536; let (l, r) := r.bytes 10; let (rest, r) := r.bytes 4
      ((if k == 0 then Sum.inl n else Sum.inr (bytes l), rest), r))
    (fun (x, rest) => roundTrip sumCodec x rest fun
      | .inl a, .inl b => a == b
      | .inr a, .inr b => a.data.toList == b.data.toList
      | _, _ => false)
    (fun (_, rest) => toString rest),
  prop "Codec.refine round-trips and rejects odd values"
    (fun r => let (n, r) := r.nat 65536; let (rest, r) := r.bytes 4; ((n, rest), r))
    (fun (n, rest) =>
      if h : n % 2 = 0 then roundTrip evenCodec ⟨n, h⟩ rest (·.val == ·.val)
      else (evenCodec.decodeBytes ((Codec.natBE 2).encodeBytes n)).isNone)
    toString,
  prop "Codec.map round-trips along its inverse"
    (fun r => let (n, r) := r.nat 128; let (rest, r) := r.bytes 4; ((n, rest), r))
    (fun (n, rest) => roundTrip doubled n rest (· == ·))
    toString,
  prop "Codec.sigma: the tag chooses the body"
    (fun r => let (t, r) := r.nat 256; let (n, r) := r.nat 256; let (rest, r) := r.bytes 4; ((t, n, rest), r))
    (fun (t, n, rest) => roundTrip tagged ⟨t, n⟩ rest fun a b => a.1 == b.1 && a.2 == b.2)
    toString,
  prop "Codec.token and rest round-trip"
    (fun r => r.bytes 10)
    (fun l => (Codec.rest : Codec UInt8 (List UInt8)).decode l == some (l, []) &&
      match l with
      | [] => true
      | b :: l' => (Codec.token : Codec UInt8 UInt8).decode (b :: l') == some (b, l'))
    toString,
  -- Refine
  prop "Refine.validate succeeds exactly when the constraint holds"
    (fun r => let (x, r) := r.nat 200; let (lo, r) := r.nat 100; let (k, r) := r.nat 9; ((x, lo, k + 1), r))
    (fun (x, lo, k) =>
      let c : Constraint Int := .and (.ge (lo : Int)) (.or (.multipleOf (k : Int)) (.not (.lt 150)))
      let x : Int := (x : Int) - 20
      (c.validate x matches .ok _) == decide (c.holds x))
    toString,
  prop "Refine.each locates every error under its index"
    (fun r => r.list 8 (fun r => r.nat 20))
    (fun xs =>
      let v := Validator.ofConstraint (Constraint.le (10 : Nat))
      match Validator.each v xs with
      | .ok ys => ys.map (·.val) == xs
      | .error es =>
        es.length == (xs.filter (· > 10)).length &&
          es.all fun e => match e.loc with
            | [.index i] => decide ((xs.getD i 0) > 10)
            | _ => false)
    toString,
  prop "Refine: a string constraint and its refinement agree"
    (fun r => let (n, r) := r.nat 12; r.list n (fun r => r.char ['a', 'b', '/']) |> fun (cs, r) => (String.ofList cs, r))
    (fun s =>
      let c : Constraint String := .and (.minLength 3) (.maxLength 8)
      (c.refine s matches .ok _) == (3 ≤ s.length && s.length ≤ 8))
    id,
  -- Route
  prop "Route.match_urlFor for int and str captures"
    (fun r => let (n, r) := r.nat 100000; let (k, r) := r.nat 10
      let (cs, r) := r.list (k + 1) (fun r => r.char ['a', 'Z', '-', '.', ':', '%']); ((n, String.ofList cs), r))
    (fun (n, s) =>
      let t := path% "/users/{name}/posts/{id:int}"
      t.match (t.urlFor (s, n, ())) == some (s, n, ()))
    toString,
  prop "Route: a uuid matches in any case and hyphenation, to one value"
    (fun r => r.list 32 (fun r => r.char "0123456789abcdef".toList))
    (fun hex =>
      let t := path% "/{id:uuid}"
      let plain := String.ofList hex
      let upper := String.ofList (hex.map Char.toUpper)
      match t.match ("/" ++ plain), t.match ("/" ++ upper) with
      | some (u, _), some (u', _) =>
        Convertor.renderUUID u == Convertor.renderUUID u' && (u.digits == hex)
      | _, _ => false)
    (fun h => String.ofList h),
  prop "Route.dispatch takes the first full match; 405 lists the first partial route"
    (fun r => let (m, r) := r.nat 4; let (n, r) := r.nat 1000; ((m, n), r))
    (fun (m, n) =>
      let method := ["GET", "PUT", "POST", "DELETE"].getD m "GET"
      let routes : List (Route String) :=
        [{ path := path% "/a/{x:int}", methods := some ["GET"], endpoint := "get" },
         { path := path% "/a/{x:int}", methods := some ["PUT"], endpoint := "put" },
         { path := path% "/a/{x:path}", methods := some ["POST"], endpoint := "post" }]
      (match Router.resolve routes method s!"/a/{n}" with
      | .found r _ => r.endpoint == method.toLower
      | .methodNotAllowed _ allow => method == "DELETE" && allow == ["GET"]
      | .notFound => false) &&
      (match Router.resolve routes method s!"/a/{n}" .unionOfPartials with
      | .found r _ => r.endpoint == method.toLower
      | .methodNotAllowed _ allow => method == "DELETE" && allow == ["GET", "PUT", "POST"]
      | .notFound => false))
    toString
]

def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:p.cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({p.cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
