import Keel

/-!
# Conformance cases

lean-keel has no upstream of its own, but `Keel.Route` models starlette's
routing, so the routing cases here re-express starlette's own tests
(`upstream-spec/starlette/tests/`). Mounts, hosts and websockets belong to
lean-starlette and are not exercised here.

Run with `lake exe conformance`.
-/

open Keel

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_path.py::test_int`. -/
  upstream : String
  name : String
  run : IO Bool

/-- What a router does, as text: the endpoint, `405 <allow>` or `404`. -/
def outcome {α : Type} [ToString α] (rs : List (Route α)) (method path : String) : String :=
  match Router.resolve rs method path with
  | .found r _ => toString r.endpoint
  | .methodNotAllowed _ allow => s!"405 {allow}"
  | .notFound => "404"

/-- The flat part of starlette's test application (`tests/test_routing.py`):
the `/users` mount's routes are written with their prefix. A function
endpoint without `methods` gets `GET` (and so `HEAD`), as in starlette. -/
def get : Option (List String) := some ["GET", "HEAD"]

def app : List (Route String) :=
  [ { path := path% "/", methods := some ["GET", "HEAD"], endpoint := "Hello, world" },
    { path := path% "/users", methods := get, endpoint := "All users" },
    { path := path% "/users/me", methods := get, endpoint := "User fixed me" },
    { path := path% "/users/{username}", methods := get, endpoint := "user" },
    { path := path% "/users/{username}:disable", methods := some ["PUT"], endpoint := "disable" },
    { path := path% "/users/nomatch", methods := get, endpoint := "User nomatch" },
    { path := path% "/func", methods := some ["GET", "HEAD"], endpoint := "func" },
    { path := path% "/func", methods := some ["POST"], endpoint := "contact" },
    { path := path% "/int/{param:int}", methods := get, endpoint := "int" },
    { path := path% "/float/{param:float}", methods := get, endpoint := "float" },
    { path := path% "/path/{param:path}", methods := get, endpoint := "path" },
    { path := path% "/uuid/{param:uuid}", methods := get, endpoint := "uuid" },
    { path := path% "/path-with-parentheses({param:int})", methods := get, endpoint := "parens" } ]

abbrev intT := path% "/int/{param:int}"
abbrev floatT := path% "/float/{param:float}"
abbrev pathT := path% "/path/{param:path}"
abbrev uuidT := path% "/uuid/{param:uuid}"
abbrev parensT := path% "/path-with-parentheses({param:int})"
abbrev userT := path% "/users/{username}"
abbrev disableT := path% "/users/{username}:disable"
abbrev floatRoot := path% "/{param:float}"
abbrev uuidRoot := path% "/{param:uuid}"

def uuidText (u : Convertor.UUID) : String := String.ofList (Convertor.renderUUID u)

def compileError (s : String) : String :=
  match PathTemplate.compile s with
  | .ok _ => "ok"
  | .error e => e

def check (b : Bool) : IO Bool := pure b

/-! ## STYLE.md section 1, as written: these must elaborate -/

def pct (x : Nat ∣ le 100) : Nat := x.val

structure Offer where
  price    : Int ∣ gt 0
  discount : Nat ∣ le 100 := 0

def search (q : Option (String ∣ maxLength 50 ∧ minLength 3) := none) : String :=
  match q with
  | some s => s.val
  | none => "<none>"

def greet (name : String ∣ minLength 1 := "anon") : String := s!"hi {name.val}"

-- The types are exactly the refinements: no leaked implicit arguments.
example : (@pct : Refined Nat (Constraint.le 100) → Nat) = pct := rfl
example : (@Offer.mk : Refined Int (Constraint.gt 0) → Refined Nat (Constraint.le 100) → Offer) =
  Offer.mk := rfl
-- Divisibility keeps its meaning under `open Keel`.
example (k n m : Nat) (h : k ∣ n ∧ k ∣ m) : k ∣ n := h.1
example : (3 : Nat) ∣ 6 := ⟨2, rfl⟩

def fruits : List String := ["Orange", "Apple"]

def pickFruit (s : String) : Option String :=
  match Constraint.pick String.toLower fruits s with
  | .ok c => some c.val
  | .error _ => none

def outcomeWith {α : Type} [ToString α] (policy : AllowPolicy) (rs : List (Route α))
    (method path : String) : String :=
  match Router.resolve rs method path policy with
  | .found r _ => toString r.endpoint
  | .methodNotAllowed _ allow => s!"405 {allow}"
  | .notFound => "404"

/-! ### Regex assertions, against Rust's `regex`

The line, CRLF-line, ASCII-word and half-boundary assertions read as Rust's
`regex` 1.12 (pydantic-core's engine, `upstream-spec/pydantic-core/Cargo.toml`)
reads `(?m)^ $`, `(?mR)^ $`, `(?-u:\b \B \< \>)` and `\b{start-half}`,
`\b{end-half}`: each expectation is `is_match` there, run through
`str_schema(pattern=..., regex_engine='rust-regex')`. The test dialect has
single characters and Unicode word characters (`é` among them). -/

inductive RxAtom where
  | char (c : Char)
  deriving DecidableEq, Hashable, Repr

instance : CharClass RxAtom where
  test | .char a, c => c == a
  word c := c.isAlphanum || c == '_' || c == 'é'

/-- A pattern as a sequence of characters and assertions. -/
inductive RxPiece where
  | c (ch : Char)
  | a (x : Regex.Assertion)

def RxPiece.term : RxPiece → Regex RxAtom
  | .c ch => .cls (.char ch)
  | .a x => .assert x

def rxSeq (ps : List RxPiece) : Regex RxAtom := ps.foldr (fun p r => .cat p.term r) .eps

/-- Rust's `is_match` of `pat` on `text` is `expect`: the scan and the
compiled matcher (whose tables must build) both say so. -/
def rust (pat : String) (ps : List RxPiece) (text : String) (expect : Bool) : Case :=
  ⟨s!"regex 1.12 is_match {pat}", s!"{pat} on {reprStr text}",
    check (let r := rxSeq ps
      (Regex.Nfa.build r).isSome && r.accepts .search text.toList == expect && (r.compile).test text == expect)⟩

def rep (s : String) (n : Nat) : String := String.join (List.replicate n s)

open RxPiece Regex.Assertion in
def rxCases : List Case := [
  rust "(?m)^b" [a lineStart, c 'b'] "a\nb" true,
  rust "(?m)^b" [a lineStart, c 'b'] "ab" false,
  rust "(?m)a$" [c 'a', a lineEnd] "a\nb" true,
  rust "(?m)a$" [c 'a', a lineEnd] "a\r\n" false,
  rust "(?m)^$" [a lineStart, a lineEnd] "" true,
  rust "(?m)\\n^" [c '\n', a lineStart] "\n" true,
  rust "(?m)\\r^" [c '\r', a lineStart] "\rx" false,
  rust "(?m)^b" [a lineStart, c 'b'] (rep "a\n" 200 ++ "b") true,
  rust "(?m)^b" [a lineStart, c 'b'] (rep "a\n" 200 ++ "ab") false,
  rust "(?mR)^b" [a lineStartCRLF, c 'b'] "a\rb" true,
  rust "(?mR)^\\n" [a lineStartCRLF, c '\n'] "\r\n" false,
  rust "(?mR)^\\n" [a lineStartCRLF, c '\n'] "\n" true,
  rust "(?mR)\\r^" [c '\r', a lineStartCRLF] "\r\n" false,
  rust "(?mR)\\r^" [c '\r', a lineStartCRLF] "\rx" true,
  rust "(?mR)\\r$" [c '\r', a lineEndCRLF] "\r\n" false,
  rust "(?mR)\\r$" [c '\r', a lineEndCRLF] "\r" true,
  rust "(?mR)\\r$" [c '\r', a lineEndCRLF] "\rx" false,
  rust "(?mR)a$" [c 'a', a lineEndCRLF] "a\r\n" true,
  rust "(?mR)\\n$" [c '\n', a lineEndCRLF] "\r\n" true,
  rust "(?mR)\\n$" [c '\n', a lineEndCRLF] "x\n" true,
  rust "(?mR)\\r$" [c '\r', a lineEndCRLF] (rep "\r\n" 200) false,
  rust "(?mR)\\r$" [c '\r', a lineEndCRLF] (rep "\r\n" 200 ++ "\r") true,
  rust "(?-u:\\b)é" [a wordBoundaryAscii, c 'é'] " é" false,
  rust "\\bé" [a wordBoundary, c 'é'] " é" true,
  rust "(?-u:\\B)é" [a notWordBoundaryAscii, c 'é'] " é" true,
  rust "\\Bé" [a notWordBoundary, c 'é'] " é" false,
  rust "(?-u:\\<)a" [a wordStartAscii, c 'a'] "éa" true,
  rust "\\<a" [a wordStart, c 'a'] "éa" false,
  rust "a(?-u:\\>)" [c 'a', a wordEndAscii] "aé" true,
  rust "a\\>" [c 'a', a wordEnd] "aé" false,
  rust "\\b{start-half}b" [a wordStartHalf, c 'b'] "ab" false,
  rust "\\b{start-half}b" [a wordStartHalf, c 'b'] " b" true,
  rust "\\b{start-half} " [a wordStartHalf, c ' '] "  " true,
  rust "a\\b{end-half}" [c 'a', a wordEndHalf] "ab" false,
  rust "a\\b{end-half}" [c 'a', a wordEndHalf] "a " true,
  rust "a\\b{end-half}" [c 'a', a wordEndHalf] "a" true,
  rust "a(?-u:\\b{end-half})" [c 'a', a wordEndHalfAscii] "aé" true,
  rust "a\\b{end-half}" [c 'a', a wordEndHalf] "aé" false,
  rust "(?-u:\\b{start-half})a" [a wordStartHalfAscii, c 'a'] "éa" true,
  rust "\\b{start-half}a" [a wordStartHalf, c 'a'] "éa" false
]

def cases : List Case := [
  -- tests/test_routing.py::test_router
  ⟨"tests/test_routing.py::test_router", "GET / runs the homepage", check (outcome app "GET" "/" == "Hello, world")⟩,
  ⟨"tests/test_routing.py::test_router", "POST / is 405 with Allow GET, HEAD",
    check (outcome app "POST" "/" == "405 [GET, HEAD]")⟩,
  ⟨"tests/test_routing.py::test_router", "GET /foo is 404", check (outcome app "GET" "/foo" == "404")⟩,
  ⟨"tests/test_routing.py::test_router", "GET /users", check (outcome app "GET" "/users" == "All users")⟩,
  ⟨"tests/test_routing.py::test_router", "GET /users/tomchristie captures the username",
    check (outcome app "GET" "/users/tomchristie" == "user" &&
      (userT.match "/users/tomchristie").map (·.1) == some "tomchristie")⟩,
  ⟨"tests/test_routing.py::test_router", "GET /users/me: the first match wins",
    check (outcome app "GET" "/users/me" == "User fixed me")⟩,
  ⟨"tests/test_routing.py::test_router", "PUT /users/tomchristie:disable",
    check (outcome app "PUT" "/users/tomchristie:disable" == "disable" &&
      (disableT.match "/users/tomchristie:disable").map (·.1) == some "tomchristie")⟩,
  ⟨"tests/test_routing.py::test_router", "GET /users/nomatch is caught by /users/{username} first",
    check (outcome app "GET" "/users/nomatch" == "user")⟩,
  -- tests/test_routing.py::test_router (/func: one path, two routes by method)
  ⟨"tests/test_routing.py::test_router", "POST /func runs the second route of the same path",
    check (outcome app "POST" "/func" == "contact" && outcome app "GET" "/func" == "func")⟩,
  ⟨"tests/test_routing.py::test_router", "DELETE /func is 405 with the first partial route's methods",
    check (outcome app "DELETE" "/func" == "405 [GET, HEAD]")⟩,
  -- tests/test_routing.py::test_route_converters
  ⟨"tests/test_routing.py::test_route_converters", "int: /int/5 is 5 and url_path_for(5) is /int/5",
    check (intT.match "/int/5" == some (5, ()) && intT.urlFor (5, ()) == "/int/5")⟩,
  ⟨"tests/test_routing.py::test_route_converters", "path with parentheses: /path-with-parentheses(7)",
    check (parensT.match "/path-with-parentheses(7)" == some (7, ()) &&
      parensT.urlFor (7, ()) == "/path-with-parentheses(7)")⟩,
  ⟨"tests/test_routing.py::test_route_converters", "float: /float/25.5 and back",
    check ((floatT.match "/float/25.5").map (fun (x, _) => (x.whole, x.frac)) == some (25, ['5']) &&
      floatT.urlFor (⟨25, ['5']⟩, ()) == "/float/25.5")⟩,
  ⟨"tests/test_routing.py::test_route_converters", "path: /path/some/example and back",
    check (pathT.match "/path/some/example" == some ("some/example", ()) &&
      pathT.urlFor ("some/example", ()) == "/path/some/example")⟩,
  ⟨"tests/test_routing.py::test_route_converters", "uuid: canonical text round-trips",
    check ((uuidT.match "/uuid/ec38df32-ceda-4cfa-9b4a-1aeb94ad551a").map (fun (u, _) => uuidText u) ==
      some "ec38df32-ceda-4cfa-9b4a-1aeb94ad551a")⟩,
  -- tests/test_routing.py::test_url_path_for
  ⟨"tests/test_routing.py::test_url_path_for", "url_path_for(user, username=tomchristie)",
    check (userT.urlFor ("tomchristie", ()) == "/users/tomchristie")⟩,
  ⟨"tests/test_routing.py::test_url_path_for", "str values with '/' or empty are not valid",
    check (!(Convertor.str.accepts "tom/christie".toList) && !(Convertor.str.accepts []))⟩,
  -- tests/test_convertors.py::test_default_float_convertor
  ⟨"tests/test_convertors.py::test_default_float_convertor", "/1.0 matches a float",
    check (floatRoot.match "/1.0" |>.isSome)⟩,
  ⟨"tests/test_convertors.py::test_default_float_convertor", "/1-0 does not",
    check (floatRoot.match "/1-0" |>.isNone)⟩,
  -- tests/test_convertors.py::test_default_uuid_convertor
  ⟨"tests/test_convertors.py::test_default_uuid_convertor", "hyphenated lower case",
    check (uuidRoot.match "/00000000-aaaa-ffff-9999-000000000000" |>.isSome)⟩,
  ⟨"tests/test_convertors.py::test_default_uuid_convertor", "no hyphens",
    check (uuidRoot.match "/00000000aaaaffff9999000000000000" |>.isSome)⟩,
  ⟨"tests/test_convertors.py::test_default_uuid_convertor", "hyphenated upper case",
    check (uuidRoot.match "/00000000-AAAA-FFFF-9999-000000000000" |>.isSome)⟩,
  ⟨"tests/test_convertors.py::test_default_uuid_convertor", "upper case, no hyphens, same value",
    check ((uuidRoot.match "/00000000AAAAFFFF9999000000000000").map (fun (u, _) => uuidText u) ==
      some "00000000-aaaa-ffff-9999-000000000000")⟩,
  ⟨"tests/test_convertors.py::test_default_uuid_convertor", "not-a-uuid",
    check (uuidRoot.match "/not-a-uuid" |>.isNone)⟩,
  -- tests/test_routing.py::test_duplicated_param_names
  ⟨"tests/test_routing.py::test_duplicated_param_names", "one duplicate",
    check (compileError "/{id}/{id}" == "Duplicated param name id at path /{id}/{id}")⟩,
  ⟨"tests/test_routing.py::test_duplicated_param_names", "two duplicates, sorted",
    check (compileError "/{id}/{name}/{id}/{name}" ==
      "Duplicated param names id, name at path /{id}/{name}/{id}/{name}")⟩,
  -- starlette/routing.py compile_path: unknown convertor
  ⟨"starlette/routing.py::compile_path", "unknown convertor",
    check (compileError "/{x:foo}" == "Unknown path convertor 'foo'")⟩,
  -- starlette/routing.py PARAM_REGEX: a '{' that is not a parameter is literal
  ⟨"starlette/routing.py::PARAM_REGEX", "a stray brace is literal",
    check (match PathTemplate.compile "/a{/b" with
      | .ok t => t.match "/a{/b" |>.isSome
      | .error _ => false)⟩,
  -- STYLE.md section 1: refinement types in signatures, fields and defaults
  ⟨"STYLE.md section 1", "a refined argument is called with a literal", check (pct 50 == 50)⟩,
  ⟨"STYLE.md section 1", "a refined field defaults to a literal",
    check (({ price := 3 } : Offer).discount.val == 0 && ({ price := 3 } : Offer).price.val == 3)⟩,
  ⟨"STYLE.md section 1", "an optional refined query parameter",
    check (search == "<none>" && search (some "abc") == "abc")⟩,
  ⟨"STYLE.md section 1", "a refined string default", check (greet == "hi anon" && greet "bo" == "hi bo")⟩,
  -- click's case-insensitive Choice returns the declared choice
  ⟨"tests/test_options.py::test_case_insensitive_choice", "apple, oRANGe and Apple pick the declared choice",
    check (pickFruit "apple" == some "Apple" && pickFruit "oRANGe" == some "Orange" &&
      pickFruit "Apple" == some "Apple")⟩,
  ⟨"tests/test_options.py::test_case_insensitive_choice", "a non-choice is rejected",
    check (pickFruit "pear" == none)⟩,
  -- the Allow policy (UP-027)
  ⟨"tests/test_routing.py::test_router", "unionOfPartials lists every partial route's methods, once",
    check (outcomeWith .unionOfPartials app "DELETE" "/func" == "405 [GET, HEAD, POST]")⟩,
  ⟨"tests/test_routing.py::test_router", "firstPartial lists the first partial route's methods",
    check (outcomeWith .firstPartial app "DELETE" "/func" == "405 [GET, HEAD]")⟩,
  -- UP-030: starlette's '$' accepts a trailing newline; Keel matches the whole path
  ⟨"UP-030 (starlette/routing.py::compile_path)", "a trailing newline does not match an int route",
    check (intT.match "/int/5\n" |>.isNone)⟩,
  -- UP-031: url_path_for substitutes sequentially; Keel inserts values verbatim
  ⟨"UP-031 (starlette/routing.py::replace_params)", "a value that looks like a placeholder is kept",
    check ((path% "/{a}/{b}").urlFor ("{b}", "x", ()) == "/{b}/x" &&
      (path% "/{a}/{b}").match "/{b}/x" == some ("{b}", "x", ()))⟩,
  -- CPython's int() refuses more than sys.int_max_str_digits (4300) digits
  ⟨"CPython int_max_str_digits (starlette/convertors.py::IntegerConvertor)",
    "an int capture takes at most 4300 digits",
    check ((intT.match ("/int/" ++ String.ofList (List.replicate 4300 '7'))).isSome &&
      (intT.match ("/int/" ++ String.ofList (List.replicate 4301 '7'))).isNone)⟩
]

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases ++ rxCases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length + rxCases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
