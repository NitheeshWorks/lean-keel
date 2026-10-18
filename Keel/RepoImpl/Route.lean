import Keel.DataTypes.Route

/-!
# Routing: matching, rendering, dispatch

* `PathTemplate.split` finds the capture texts of a path with starlette's
  regular-expression semantics: literals match exactly, and each capture
  takes the longest text its convertor accepts for which the rest of the
  template still matches (greedy, with backtracking). It is total: each
  capture tries finitely many prefix lengths, and the recursion is on the
  pieces.
* `PathTemplate.match` converts the texts; `urlFor` renders values back
  (starlette's `url_path_for` on one route).
* `dispatch` is first-match over any list of routes with a three-way match,
  and `Router.resolve` is starlette's `Router` decision: the first full match,
  else `405` with the first partial match's methods, else `404`.
-/

namespace Keel

namespace Acceptor

/-- The accepted prefixes of `s`, after reading `pre` (reversed) into state
`q`: each as its text (reversed) and the rest of `s`, longest first, in front
of `acc`. One tail-recursive pass, which ends where the automaton stops. -/
def cuts (a : Acceptor) : a.State → List Char → List Char → List (List Char × List Char) →
    List (List Char × List Char)
  | q, pre, [], acc => if a.final q then (pre, []) :: acc else acc
  | q, pre, c :: cs, acc =>
    let acc := if a.final q then (pre, c :: cs) :: acc else acc
    match a.step q c with
    | none => acc
    | some q' => a.cuts q' (c :: pre) cs acc

theorem run_append (a : Acceptor) : ∀ (q : a.State) (t u : List Char),
    a.run q (t ++ u) = (a.run q t).bind (a.run · u)
  | q, [], u => rfl
  | q, c :: cs, u => by
    show (a.step q c).bind (a.run · (cs ++ u)) = ((a.step q c).bind (a.run · cs)).bind (a.run · u)
    cases a.step q c with
    | none => rfl
    | some q' => exact run_append a q' cs u

end Acceptor

namespace PathTemplate

/-- The path that the capture texts spell out, in order of the captures. -/
def urlTexts : List Piece → List (List Char) → List Char
  | [], _ => []
  | .lit l :: ps, ts => l ++ urlTexts ps ts
  | .cap _ _ :: ps, t :: ts => t ++ urlTexts ps ts
  | .cap _ _ :: ps, [] => urlTexts ps []

/-- The texts of the values, in order. -/
def renderArgs : (ps : List Piece) → Args ps → List (List Char)
  | [], _ => []
  | .lit _ :: ps, v => renderArgs ps v
  | .cap _ c :: ps, (x, v) => c.render x :: renderArgs ps v

/-- The first `some` among `f n, f (n - 1), …, f 0`. -/
def firstDown {β : Type} (f : Nat → Option β) : Nat → Option β
  | 0 => f 0
  | n + 1 =>
    match f (n + 1) with
    | some b => some b
    | none => firstDown f n

/-- The capture texts of a path, greedily, as a regular expression would
find them. -/
def split : List Piece → List Char → Option (List (List Char))
  | [], s => if s = [] then some [] else none
  | .lit l :: ps, s => if l <+: s then split ps (s.drop l.length) else none
  | .cap _ c :: ps, s =>
    firstDown (fun k =>
      if c.accepts (s.take k) then (split ps (s.drop k)).map (s.take k :: ·) else none)
      s.length

/-! ## The split in one pass

`split` is the specification: for a capture it tries every prefix length,
longest first, and tests each prefix afresh, which is quadratic in the path.
`splitFast` finds all the accepted prefixes in one pass of the convertor's
`Acceptor` (`Acceptor.cuts`, tail-recursive, stopping where the automaton
stops: a segment convertor at the first `/`), then tries them longest first.
`split_eq_splitFast` proves them equal, and `@[csimp]` makes compiled code
run `splitFast` wherever `split` is called. -/


/-- The first `some` among `f n, …, f 0` is the first among `f n, …, f 1`,
else `f 0`. -/
theorem firstDown_succ {β : Type} (f : Nat → Option β) :
    ∀ n, firstDown f (n + 1) = (firstDown (fun k => f (k + 1)) n).or (f 0)
  | 0 => by
    show (match f 1 with | some b => some b | none => f 0) = (f 1).or (f 0)
    cases f 1 <;> rfl
  | n + 1 => by
    show (match f (n + 2) with | some b => some b | none => firstDown f (n + 1)) =
      (match f (n + 2) with | some b => some b | none => firstDown (fun k => f (k + 1)) n).or (f 0)
    cases f (n + 2) with
    | some b => rfl
    | none => exact firstDown_succ f n

theorem firstDown_none {β : Type} {f : Nat → Option β} (h : ∀ k, f k = none) :
    ∀ n, firstDown f n = none
  | 0 => h 0
  | n + 1 => by
    show (match f (n + 1) with | some b => some b | none => firstDown f n) = none
    rw [h (n + 1)]; exact firstDown_none h n

theorem findSome?_cons_or {α β : Type} (f : α → Option β) (x : α) (l : List α) :
    (x :: l).findSome? f = (f x).or (l.findSome? f) := by
  simp only [List.findSome?]; cases f x <;> rfl

/-- The longest-first search of `split` for one capture, after the text `p`:
the first prefix `p ++ s.take k`, longest first, that `test` accepts and for
which `g` succeeds on the text and the rest. -/
def capSearch {β : Type} (test : List Char → Bool) (g : List Char → List Char → Option β)
    (p s : List Char) : Option β :=
  firstDown (fun k => if test (p ++ s.take k) then g (p ++ s.take k) (s.drop k) else none) s.length

theorem capSearch_nil {β : Type} (test : List Char → Bool) (g : List Char → List Char → Option β)
    (p : List Char) : capSearch test g p [] = if test p then g p [] else none := by
  simp [capSearch, firstDown]

theorem capSearch_cons {β : Type} (test : List Char → Bool) (g : List Char → List Char → Option β)
    (p : List Char) (c : Char) (cs : List Char) :
    capSearch test g p (c :: cs) =
      (capSearch test g (p ++ [c]) cs).or (if test p then g p (c :: cs) else none) := by
  simp only [capSearch, List.length_cons]
  rw [firstDown_succ]
  simp [List.take_succ_cons, List.drop_succ_cons, List.append_assoc]

/-- The one-pass search agrees with `capSearch`, for an automaton that has
read `pre` (reversed). -/
theorem findSome?_cuts {β : Type} (a : Acceptor) (g : List Char → List Char → Option β) :
    ∀ (s : List Char) (q : a.State) (pre : List Char) (acc : List (List Char × List Char)),
      a.run a.start pre.reverse = some q →
      (a.cuts q pre s acc).findSome? (fun x => g x.1.reverse x.2) =
        (capSearch a.accepts g pre.reverse s).or (acc.findSome? fun x => g x.1.reverse x.2)
  | [], q, pre, acc, hq => by
    have hf : a.accepts pre.reverse = a.final q := by simp [Acceptor.accepts, hq, Option.any]
    simp only [Acceptor.cuts, capSearch_nil, hf]
    cases a.final q <;> simp [findSome?_cons_or]
  | c :: cs, q, pre, acc, hq => by
    have hf : a.accepts pre.reverse = a.final q := by simp [Acceptor.accepts, hq, Option.any]
    have hacc : (List.findSome? (fun x => g x.1.reverse x.2)
        (if a.final q then (pre, c :: cs) :: acc else acc)) =
        (if a.final q then g pre.reverse (c :: cs) else none).or
          (acc.findSome? fun x => g x.1.reverse x.2) := by
      cases a.final q <;> simp [findSome?_cons_or]
    rw [capSearch_cons, hf, Option.or_assoc, ← hacc]
    simp only [Acceptor.cuts]
    have hrun : a.run a.start (pre.reverse ++ [c]) = a.step q c := by
      rw [Acceptor.run_append, hq]
      show (a.step q c).bind (a.run · []) = a.step q c
      cases a.step q c <;> rfl
    cases hs : a.step q c with
    | none =>
      have hdead : capSearch a.accepts g (pre.reverse ++ [c]) cs = none := by
        apply firstDown_none
        intro k
        have : a.accepts (pre.reverse ++ [c] ++ cs.take k) = false := by
          simp only [Acceptor.accepts]
          rw [Acceptor.run_append, hrun, hs]; rfl
        simp only [this]; rfl
      simp [hdead]
    | some q' =>
      have hq' : a.run a.start (c :: pre).reverse = some q' := by
        rw [List.reverse_cons, hrun, hs]
      rw [findSome?_cuts a g cs q' (c :: pre) _ hq', List.reverse_cons]

/-- `split`, finding each capture's accepted prefixes in one pass. -/
def splitFast : List Piece → List Char → Option (List (List Char))
  | [], s => if s = [] then some [] else none
  | .lit l :: ps, s => if l <+: s then splitFast ps (s.drop l.length) else none
  | .cap _ c :: ps, s =>
    (c.acceptor.cuts c.acceptor.start [] s []).findSome? fun x =>
      (splitFast ps x.2).map (x.1.reverse :: ·)

theorem split_eq_splitFast : ∀ (ps : List Piece) (s : List Char), split ps s = splitFast ps s
  | [], s => rfl
  | .lit l :: ps, s => by
    simp only [split, splitFast, split_eq_splitFast ps]
  | .cap _ c :: ps, s => by
    have hacc : c.acceptor.accepts = c.accepts := funext c.acceptor_accepts
    have h := findSome?_cuts c.acceptor (fun t r => (splitFast ps r).map (t :: ·)) s
      c.acceptor.start [] [] rfl
    simp only [List.reverse_nil, List.findSome?_nil, Option.or_none, hacc] at h
    simp only [split, splitFast, h, capSearch, List.nil_append, split_eq_splitFast ps]

@[csimp] theorem split_csimp : @split = @splitFast :=
  funext fun ps => funext fun s => split_eq_splitFast ps s

/-- Convert the capture texts, in order. -/
def convert : (ps : List Piece) → List (List Char) → Option (Args ps)
  | [], [] => some ()
  | [], _ :: _ => none
  | .lit _ :: ps, ts => convert ps ts
  | .cap _ _ :: _, [] => none
  | .cap _ c :: ps, t :: ts =>
    match c.parse t, convert ps ts with
    | some x, some v => some (x, v)
    | _, _ => none

/-- Match a path given as characters. -/
def matchPieces (ps : List Piece) (s : List Char) : Option (Args ps) := (split ps s).bind (convert ps)

/-- **Match** a path against the template: the converted captures, if it
matches. -/
def «match» (t : PathTemplate) (path : String) : Option (Args t.pieces) :=
  matchPieces t.pieces path.toList

/-- **The URL** of the template for the given values. -/
def urlFor (t : PathTemplate) (v : Args t.pieces) : String :=
  String.ofList (urlTexts t.pieces (renderArgs t.pieces v))

/-- Every value is one its convertor can render. -/
def ArgsValid : (ps : List Piece) → Args ps → Prop
  | [], _ => True
  | .lit _ :: ps, v => ArgsValid ps v
  | .cap _ c :: ps, (x, v) => c.Valid x ∧ ArgsValid ps v

/-- Every text is one its convertor accepts, one text per capture. -/
def TextsAccepted : List Piece → List (List Char) → Prop
  | [], ts => ts = []
  | .lit _ :: ps, ts => TextsAccepted ps ts
  | .cap _ _ :: _, [] => False
  | .cap _ c :: ps, t :: ts => c.accepts t = true ∧ TextsAccepted ps ts

/-- A text is canonical for a convertor when it is the rendering of what it
converts to: `7` for an `int`, not `007`. -/
def _root_.Keel.Convertor.Canonical (c : Convertor) (t : List Char) : Prop := ∀ x, c.parse t = some x → c.render x = t

/-- Every capture text is canonical. -/
def TextsCanonical : List Piece → List (List Char) → Prop
  | [], _ => True
  | .lit _ :: ps, ts => TextsCanonical ps ts
  | .cap _ _ :: _, [] => True
  | .cap _ c :: ps, t :: ts => c.Canonical t ∧ TextsCanonical ps ts

/-- A path is in canonical form for the template: the texts it captures are
canonical. -/
def Canonical (t : PathTemplate) (path : String) : Prop :=
  ∀ ts, split t.pieces path.toList = some ts → TextsCanonical t.pieces ts

/-- Segment-aligned templates: every capture is the last piece, or is
followed by a literal that starts with `/` and uses a convertor that never
accepts `/`. Such a capture is a whole path segment (or the tail of the path),
so matching is unambiguous. `/items/{id:int}`, `/users/{u}/posts/{p}` and
`/files/{rest:path}` are aligned; `/files/{name}.{ext}` is not. -/
def aligned : List Piece → Bool
  | [] => true
  | .lit _ :: ps => aligned ps
  | [.cap _ _] => true
  | .cap _ c :: .lit l :: ps => c.segment && l.head? == some '/' && aligned (.lit l :: ps)
  | .cap _ _ :: .cap _ _ :: _ => false

/-- The template is segment-aligned. -/
abbrev Aligned (t : PathTemplate) : Prop := aligned t.pieces = true

/-- The names of the captures. -/
def names : List Piece → List String
  | [] => []
  | .lit _ :: ps => names ps
  | .cap n _ :: ps => n :: names ps

/-- The captured values, by name, as text (starlette's `path_params`, rendered). -/
def namedTexts : (ps : List Piece) → Args ps → List (String × String)
  | [], _ => []
  | .lit _ :: ps, v => namedTexts ps v
  | .cap n c :: ps, (x, v) => (n, String.ofList (c.render x)) :: namedTexts ps v

end PathTemplate

/-! ## First-match dispatch -/

namespace Match

variable {β : Type}

/-- A full match. -/
def IsFull : Match β → Prop
  | .full _ => True
  | _ => False

instance (m : Match β) : Decidable m.IsFull := by
  cases m <;> simp only [IsFull] <;> infer_instance

/-- Whether a match is partial. -/
def isPartial : Match β → Bool
  | .partial => true
  | _ => false

theorem isPartial_iff (m : Match β) : m.isPartial = true ↔ m = .partial := by
  cases m <;> simp [isPartial]

end Match

/-- **First-match dispatch**: the first route that matches fully; if none
does, the first that matches partially; otherwise none. A partial match does
not stop the search for a full one. -/
def dispatch.{u} {ρ : Type u} {β : ρ → Type} (m : (r : ρ) → Match (β r)) : List ρ → Outcome ρ β
  | [] => .none
  | r :: rs =>
    match m r with
    | .full b => .found r b
    | .partial =>
      match dispatch m rs with
      | .found r' b => .found r' b
      | _ => .partial r
    | .none => dispatch m rs

/-! ## HTTP routes -/

namespace Route

variable {α : Type}

/-- Whether the route allows the method (a route without methods allows
every method). -/
def allows (r : Route α) (method : String) : Bool :=
  match r.methods with
  | none => true
  | some ms => ms.contains method

/-- How the route matches a request (starlette's `Route.matches`). -/
def «matches» (r : Route α) (method path : String) : Match (Args r.path.pieces) :=
  match r.path.match path with
  | none => .none
  | some v => if r.allows method then .full v else .partial

end Route

/-- Which methods a `405` lists in `Allow`. -/
inductive AllowPolicy where
  /-- The methods of the first route that matched the path: starlette's
  behaviour (recorded upstream as UP-027). -/
  | firstPartial
  /-- Every method of every route that matched the path, once each, in route
  order and then each route's method order. -/
  | unionOfPartials
  deriving DecidableEq, Repr, Inhabited

/-- The list without repeats, keeping first occurrences. -/
def dedup : List String → List String
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· != x)

/-- What the router does with a request. -/
inductive Resolution (α : Type) : Type 1 where
  /-- Run this route's endpoint with these captured values. -/
  | found (r : Route α) (args : Args r.path.pieces)
  /-- `405 Method Not Allowed`: the first route that matched the path, and the
  methods for `Allow`. -/
  | methodNotAllowed (r : Route α) (allow : List String)
  /-- `404 Not Found`. -/
  | notFound

/-- The methods of every route that matches the path, once each. -/
def Router.partialMethods {α : Type} (routes : List (Route α)) (method path : String) : List String :=
  dedup ((routes.filter fun r => (r.matches method path).isPartial).flatMap (·.methods.getD []))

/-- **The router**: starlette's `Router` decision for a method and a path; the
`Allow` list of a `405` follows `policy`. -/
def Router.resolve {α : Type} (routes : List (Route α)) (method path : String)
    (policy : AllowPolicy := .firstPartial) : Resolution α :=
  match dispatch (fun (r : Route α) => r.matches method path) routes with
  | .found r v => .found r v
  | .partial r =>
    .methodNotAllowed r
      (match policy with
       | .firstPartial => r.methods.getD []
       | .unionOfPartials => Router.partialMethods routes method path)
  | .none => .notFound

end Keel
