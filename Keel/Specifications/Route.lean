import Keel.APIs.Route

/-!
# Specifications: routing

The headline laws of `Keel.Route`, proved in `Proofs/Route.lean`, with slots
in `Proofs/Verified.lean`.
-/

namespace Keel.Spec

open PathTemplate

/-- An aligned template matches its own URLs, giving back the values. -/
def MatchUrlFor : Prop :=
  ∀ (t : PathTemplate) (v : Args t.pieces), t.Aligned → ArgsValid t.pieces v →
    t.match (t.urlFor v) = some v

/-- The URL of a canonical path's match is the path. -/
def UrlForMatch : Prop :=
  ∀ (t : PathTemplate) (path : String) (v : Args t.pieces), t.match path = some v →
    t.Canonical path → t.urlFor v = path

/-- Dispatch finds the first route that matches fully. -/
def DispatchFirstMatch : Prop :=
  ∀ (ρ : Type 1) (β : ρ → Type) (m : (r : ρ) → Match (β r)) (rs : List ρ) (r : ρ) (b : β r),
    dispatch m rs = .found r b ↔
      ∃ pre post, rs = pre ++ r :: post ∧ m r = .full b ∧ ∀ r' ∈ pre, ¬ (m r').IsFull

/-- Dispatch is partial exactly when nothing matches fully and something
matches partially. -/
def DispatchPartial : Prop :=
  ∀ (ρ : Type 1) (β : ρ → Type) (m : (r : ρ) → Match (β r)) (rs : List ρ),
    (∃ r, dispatch m rs = .partial r) ↔ (∀ r ∈ rs, ¬ (m r).IsFull) ∧ ∃ r ∈ rs, m r = .partial

/-- Dispatch finds nothing exactly when nothing matches. -/
def DispatchNone : Prop :=
  ∀ (ρ : Type 1) (β : ρ → Type) (m : (r : ρ) → Match (β r)) (rs : List ρ),
    dispatch m rs = .none ↔ ∀ r ∈ rs, m r = .none

/-- The router runs the first route matching method and path. -/
def ResolveFirstMatch : Prop :=
  ∀ (α : Type) (rs : List (Route α)) (method path : String) (r : Route α) (v : Args r.path.pieces),
    Router.resolve rs method path = .found r v ↔
      ∃ pre post, rs = pre ++ r :: post ∧ r.matches method path = .full v ∧
        ∀ r' ∈ pre, ¬ (r'.matches method path).IsFull

/-- 405 exactly when no route matches method and path and some route
matches the path. -/
def MethodNotAllowedIff : Prop :=
  ∀ (α : Type) (rs : List (Route α)) (method path : String),
    (∃ r allow, Router.resolve rs method path = .methodNotAllowed r allow) ↔
      (∀ r ∈ rs, ¬ (r.matches method path).IsFull) ∧ ∃ r ∈ rs, r.matches method path = .partial

/-- 404 exactly when no route matches the path. -/
def NotFoundIff : Prop :=
  ∀ (α : Type) (rs : List (Route α)) (method path : String),
    Router.resolve rs method path = .notFound ↔ ∀ r ∈ rs, r.path.match path = none

end Keel.Spec
