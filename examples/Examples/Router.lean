import Keel

/-!
# Example: a router, with both `Allow` policies

Three routes, starlette style: `GET` and `PUT` on `/items/{item_id:int}` as
two routes, and `POST /items`. The path parameter is a typed `Nat`.

Inherits: `PathTemplate.match_urlFor` (the router recognises every URL it
renders), `Router.resolve_found_iff` (first match),
`Router.methodNotAllowed_iff` (405 iff partial) and the `Allow` laws for
each policy: `methodNotAllowed_allow_first` (starlette: the first partially
matching route's methods) and `methodNotAllowed_allow_union` (every
partially matching route's methods, once each).
-/

namespace Examples.Router

open Keel

abbrev item := path% "/items/{item_id:int}"

def readItem : Route String := { path := item, methods := some ["GET", "HEAD"], endpoint := "read" }
def updateItem : Route String := { path := item, methods := some ["PUT"], endpoint := "update" }
def createItem : Route String := { path := path% "/items", methods := some ["POST"], endpoint := "create" }

def routes : List (Route String) := [readItem, updateItem, createItem]

/-- What the router decided, in short. -/
inductive Answer where
  | run (endpoint : String)
  | methodNotAllowed (allow : List String)
  | notFound
  deriving DecidableEq, Repr

def answer (policy : AllowPolicy) (method path : String) : Answer :=
  match Router.resolve routes method path policy with
  | .found r _ => .run r.endpoint
  | .methodNotAllowed _ allow => .methodNotAllowed allow
  | .notFound => .notFound

/-- The router's answer, as text, with the captured parameters. -/
def describe (policy : AllowPolicy) (method path : String) : String :=
  match Router.resolve routes method path policy with
  | .found r args => s!"{r.endpoint} {PathTemplate.namedTexts r.path.pieces args}"
  | .methodNotAllowed _ allow => s!"405 Allow: {", ".intercalate allow}"
  | .notFound => "404"

/-- Every item URL is recognised, with its id, for ids of at most
`maxIntDigits` (4300) digits, the most an `int` capture accepts. -/
theorem item_match (n : Nat) (hn : n < 10 ^ Convertor.maxIntDigits) :
    item.match (item.urlFor (n, ())) = some (n, ()) :=
  item.match_urlFor (by decide) _ ⟨hn, trivial⟩

/-- **`DELETE` on any item is a 405**, whatever the policy: two routes match
the path, none the method. -/
theorem delete_item_405 (n : Nat) (hn : n < 10 ^ Convertor.maxIntDigits) (policy : AllowPolicy) :
    ∃ r allow, Router.resolve routes "DELETE" (item.urlFor (n, ())) policy = .methodNotAllowed r allow := by
  rw [Router.methodNotAllowed_iff (policy := policy)]
  have h0 := Route.matches_of_match readItem (method := "DELETE") (item_match n hn)
  have h1 := Route.matches_of_match updateItem (method := "DELETE") (item_match n hn)
  refine ⟨?_, readItem, by simp [routes], by rw [h0]; rfl⟩
  intro r hr
  simp only [routes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h0]; simp [readItem, Route.allows, Match.IsFull]
  · rw [h1]; simp [updateItem, Route.allows, Match.IsFull]
  · simp only [Route.matches]
    split <;> simp [Route.allows, Match.IsFull, createItem]

/-! ## Both policies, concretely -/

example : answer .firstPartial "GET" "/items/42" = .run "read" := by decide
example : answer .firstPartial "PUT" "/items/42" = .run "update" := by decide
example : answer .firstPartial "DELETE" "/items/42" = .methodNotAllowed ["GET", "HEAD"] := by decide
example : answer .unionOfPartials "DELETE" "/items/42" = .methodNotAllowed ["GET", "HEAD", "PUT"] := by decide
example : answer .unionOfPartials "POST" "/items" = .run "create" := by decide
example : answer .firstPartial "GET" "/nowhere" = .notFound := by decide
example : item.match "/items/42" = some (42, ()) := by decide

def run : IO Unit := do
  for (policy, name) in [(AllowPolicy.firstPartial, "firstPartial"), (.unionOfPartials, "unionOfPartials")] do
    for (m, p) in [("GET", "/items/42"), ("PUT", "/items/7"), ("DELETE", "/items/7"),
        ("POST", "/items"), ("GET", "/items/x")] do
      IO.println s!"{name}: {m} {p} -> {describe policy m p}"

end Examples.Router
