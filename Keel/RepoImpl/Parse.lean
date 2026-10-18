import Keel.DataTypes.Parse

/-!
# Parser combinators

The primitives prove the two `Parser` invariants directly; everything else is
built from them, so it inherits the invariants for free. The primitives are:
`pure`, `bind`, `fail`, `orElse` (committed choice), `attempt`, `lookahead`,
`mapError`, `peek?`, `next?`, `satisfy`, `many`, and the recursion
combinator `fix`.

Totality. `many`, `fix` and `fixDepth` are the only recursive definitions. Both recurse
on the number of tokens left, `Input.size s - i`, by well-founded recursion:

* `many p` repeats `p` while it succeeds *and moves*. The invariants say a
  parser that moved is still in bounds, so the tokens left strictly decrease.
  A step that succeeds without consuming ends the loop.
* `fix F` ties a recursive knot. The recursive handle passed to `F` runs the
  parser only on strictly fewer tokens than the call that made it; called
  without progress (a left-recursive grammar) it fails with
  `ParseError.stuck`. Well-formed grammars never see that error, and
  `parse_fix` / `parse_below` say exactly when it can arise.
* `fixDepth max F` is `fix F` with at most `max` nested calls; past the bound
  it fails with `ParseError.depthExceeded`. Unbounded `fix` recurses as deep
  as the input nests, which on attacker input can exhaust the native stack:
  parsers of untrusted input use `fixDepth`.

Choice is committed, as in Parsec: `p <|> q` tries `q` only if `p` failed
without consuming input. `attempt p` makes a failure non-consuming.
-/

namespace Keel

namespace Parser

variable {τ ε ε' α β : Type}


theorem run_list (p : Parser τ ε α) (l : List τ) (i : Nat) :
    p.run l i = (p.run (l.drop i) 0).shift i := p.run_eq l i

/-- On success the position only moves forward, and stays within the input
(when it started there). -/
theorem run_ok_bounds {σ : Type} [Input σ τ] (p : Parser τ ε α) {s : σ} {i : Nat} {a : α} {j : Nat}
    (h : p.run s i = .ok a j) : i ≤ j ∧ j - i ≤ Input.size s - i := by
  rw [p.run_eq s i] at h
  have hle := p.pos_le (Input.rest s i)
  cases hc : p.run (Input.rest s i) 0 with
  | ok a' j' =>
    rw [hc] at h hle
    simp only [Result.shift_ok, Result.ok.injEq] at h
    simp only [Result.pos_ok, Input.length_rest] at hle
    omega
  | error e j' => rw [hc] at h; simp at h

/-- Every reported position is at or after the start and within the input
(counting from the start). -/
theorem run_pos {σ : Type} [Input σ τ] (p : Parser τ ε α) (s : σ) (i : Nat) :
    i ≤ (p.run s i).pos ∧ (p.run s i).pos ≤ i + (Input.size s - i) := by
  rw [p.run_eq s i, Result.pos_shift]
  have := p.pos_le (Input.rest s i)
  rw [Input.length_rest] at this
  omega

/-- A step that moved consumed a token: fewer tokens are left. -/
theorem ok_lt {σ : Type} [Input σ τ] (p : Parser τ ε α) {s : σ} {i : Nat} {a : α} {j : Nat}
    (h : p.run s i = .ok a j) (hj : ¬ j = i) : Input.size s - j < Input.size s - i := by
  have := p.run_ok_bounds h
  omega

/-! ## The monad -/

/-- Succeed with `a`, consuming nothing. -/
protected def pure (a : α) : Parser τ ε α where
  run _ i := .ok a i
  run_eq _ i := by simp
  pos_le _ := by simp

/-- Run `p`, then `f` on its value from where `p` stopped. -/
protected def bind (p : Parser τ ε α) (f : α → Parser τ ε β) : Parser τ ε β where
  run s i :=
    match p.run s i with
    | .ok a j => (f a).run s j
    | .error e j => .error e j
  run_eq s i := by
    rw [p.run_eq s i]
    cases p.run (Input.rest s i) 0 with
    | ok a j =>
      simp only [Result.shift_ok]
      rw [(f a).run_eq s (j + i), (f a).run_eq (Input.rest s i) j, Result.shift_shift]
      simp [Input.rest, List.drop_drop, Nat.add_comm]
    | error e j => rfl
  pos_le l := by
    have hp := p.pos_le l
    cases hc : p.run l 0 with
    | ok a j =>
      simp only [hc, Result.pos_ok] at hp ⊢
      rw [(f a).run_eq l j]
      have hf := (f a).pos_le (Input.rest l j)
      simp only [Result.pos_shift, Input.rest, Input.toList_list, List.length_drop] at hf ⊢
      omega
    | error e j => simpa [hc] using hp

instance : Monad (Parser τ ε) where
  pure := Parser.pure
  bind := Parser.bind

/-- Fail with `e` where the parser stands, consuming nothing. -/
def fail (e : ε) : Parser τ ε α where
  run _ i := .error e i
  run_eq _ i := by simp
  pos_le _ := by simp

/-- Committed choice: `p`, or, if `p` failed without consuming input, `q`. -/
protected def orElse (p : Parser τ ε α) (q : Unit → Parser τ ε α) : Parser τ ε α where
  run s i :=
    match p.run s i with
    | .ok a j => .ok a j
    | .error e j => if j = i then (q ()).run s i else .error e j
  run_eq s i := by
    rw [p.run_eq s i]
    cases p.run (Input.rest s i) 0 with
    | ok a j => rfl
    | error e j =>
      by_cases hj : j = 0
      · simp [hj, (q ()).run_eq s i]
      · simp [hj]
  pos_le l := by
    have hp := p.pos_le l
    cases hc : p.run l 0 with
    | ok a j => simpa [hc] using hp
    | error e j =>
      simp only [hc, Result.pos_error] at hp ⊢
      split
      · exact (q ()).pos_le l
      · simpa using hp

instance : OrElse (Parser τ ε α) := ⟨Parser.orElse⟩

/-- `p`, but a failure is reported where `p` started, so it counts as not
consuming and `<|>` tries the next alternative. -/
def attempt (p : Parser τ ε α) : Parser τ ε α where
  run s i :=
    match p.run s i with
    | .ok a j => .ok a j
    | .error e _ => .error e i
  run_eq s i := by
    rw [p.run_eq s i]
    cases p.run (Input.rest s i) 0 <;> simp
  pos_le l := by
    have hp := p.pos_le l
    cases hc : p.run l 0 <;> simp_all

/-- Run `p` without consuming: its value, at the position it started. -/
def lookahead (p : Parser τ ε α) : Parser τ ε α where
  run s i :=
    match p.run s i with
    | .ok a _ => .ok a i
    | .error e j => .error e j
  run_eq s i := by
    rw [p.run_eq s i]
    cases p.run (Input.rest s i) 0 <;> simp
  pos_le l := by
    have hp := p.pos_le l
    cases hc : p.run l 0 <;> simp_all

/-- Change the error type. -/
def mapError (f : ε → ε') (p : Parser τ ε α) : Parser τ ε' α where
  run s i :=
    match p.run s i with
    | .ok a j => .ok a j
    | .error e j => .error (f e) j
  run_eq s i := by
    rw [p.run_eq s i]
    cases p.run (Input.rest s i) 0 <;> simp
  pos_le l := by
    have hp := p.pos_le l
    cases hc : p.run l 0 <;> simp_all

/-- `p`, reporting `e` instead of its own error. -/
def withError (e : ε) (p : Parser τ ε α) : Parser τ ε α := p.mapError fun _ => e

@[inherit_doc withError] infixl:60 " <?> " => fun p e => Parser.withError e p

/-! ## Reading tokens -/

/-- The next token, if any, without consuming it. -/
def peek? : Parser τ ε (Option τ) where
  run s i := .ok (Input.get? s i) i
  run_eq s i := by simp [Input.get?_eq]
  pos_le _ := by simp

/-- The next token, consumed, or `none` at the end of the input. -/
def next? : Parser τ ε (Option τ) where
  run s i :=
    match Input.get? s i with
    | some t => .ok (some t) (i + 1)
    | none => .ok none i
  run_eq s i := by
    have h := Input.get?_rest s i 0
    simp only [Nat.add_zero] at h
    simp only [Input.get?_list, h]
    cases Input.get? s i <;> simp [Nat.add_comm]
  pos_le l := by
    cases l <;> simp

/-- The next token if it satisfies `f`. Fails without consuming otherwise:
`unexpected` on a token, `eof` at the end. -/
def satisfy [ParseError ε] (f : τ → Bool) : Parser τ ε τ where
  run s i :=
    match Input.get? s i with
    | some t => if f t then .ok t (i + 1) else .error ParseError.unexpected i
    | none => .error ParseError.eof i
  run_eq s i := by
    have h := Input.get?_rest s i 0
    simp only [Nat.add_zero] at h
    simp only [Input.get?_list, h]
    cases Input.get? s i with
    | none => simp
    | some t => by_cases hf : f t <;> simp [hf, Nat.add_comm]
  pos_le l := by
    cases l with
    | nil => simp
    | cons t l => by_cases hf : f t <;> simp [hf]

/-- The next token, whatever it is. -/
def next [ParseError ε] : Parser τ ε τ := satisfy fun _ => true

/-- Exactly the token `t`. -/
def token [ParseError ε] [DecidableEq τ] (t : τ) : Parser τ ε τ := satisfy fun u => decide (u = t)

/-- Succeed at the end of the input; fail with `unexpected` before it. -/
def eof [ParseError ε] : Parser τ ε Unit := do
  match ← peek? with
  | none => pure ()
  | some _ => fail ParseError.unexpected

/-- `some` of `p`'s value, or `none` if `p` failed without consuming. -/
def optional (p : Parser τ ε α) : Parser τ ε (Option α) :=
  (some <$> p) <|> pure none

/-- The tokens of `l` one after another (not atomic: see `lit`). -/
def tokens [ParseError ε] [DecidableEq τ] : List τ → Parser τ ε Unit
  | [] => pure ()
  | t :: ts => token t *> tokens ts

/-- Exactly the tokens `l`, consumed together: a mismatch fails without
consuming. -/
def lit [ParseError ε] [DecidableEq τ] (l : List τ) : Parser τ ε Unit := attempt (tokens l)

/-- Whether the input continues with `l`, without consuming anything. -/
def startsWith [ParseError ε] [DecidableEq τ] (l : List τ) : Parser τ ε Bool :=
  (lookahead (lit l) *> pure true) <|> pure false

/-- `n` tokens. -/
def take [ParseError ε] (n : Nat) : Parser τ ε (List τ) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let t ← next
    let ts ← take n
    pure (t :: ts)

/-! ## Repetition -/

/-- The loop of `many`, accumulating in reverse. -/
def manyGo (p : Parser τ ε α) {σ : Type} [Input σ τ] (s : σ) (i : Nat) (acc : List α) :
    Result ε (List α) :=
  match _h : p.run s i with
  | .ok a j => if _hj : j = i then .ok acc.reverse i else manyGo p s j (a :: acc)
  | .error e j => if j = i then .ok acc.reverse i else .error e j
termination_by Input.size s - i
decreasing_by exact p.ok_lt _h _hj

theorem manyGo_eq (p : Parser τ ε α) {σ : Type} [Input σ τ] (s : σ) (i : Nat) (acc : List α) :
    manyGo p s i acc =
      match p.run s i with
      | .ok a j => if j = i then .ok acc.reverse i else manyGo p s j (a :: acc)
      | .error e j => if j = i then .ok acc.reverse i else .error e j := by
  rw [manyGo]
  split <;> rename_i h <;> simp only [h, dite_eq_ite]

theorem manyGo_shift (p : Parser τ ε α) {σ : Type} [Input σ τ] (s : σ) :
    ∀ (n i k : Nat) (acc : List α), Input.size s - (i + k) = n →
      manyGo p s (i + k) acc = (manyGo p (Input.rest s i) k acc).shift i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i k acc hn
    have e1 := p.run_eq s (i + k)
    have e2 := p.run_eq (Input.rest s i) k
    have hcore : Input.rest (Input.rest s i) k = Input.rest s (i + k) := by
      simp [Input.rest, List.drop_drop]
    rw [hcore] at e2
    have hb := p.pos_le (Input.rest s (i + k))
    rw [Input.length_rest] at hb
    rw [manyGo_eq, manyGo_eq, e1, e2]
    generalize p.run (Input.rest s (i + k)) 0 = r at hb
    cases r with
    | ok a j₀ =>
      simp only [Result.shift_ok, Result.pos_ok] at hb ⊢
      by_cases h0 : j₀ = 0
      · subst h0; simp [Nat.add_comm]
      · have hA : ¬ j₀ + (i + k) = i + k := by omega
        have hB : ¬ j₀ + k = k := by omega
        rw [ite_eq_right hA, ite_eq_right hB]
        rw [show j₀ + (i + k) = i + (j₀ + k) by omega]
        exact ih (Input.size s - (i + (j₀ + k))) (by omega) i (j₀ + k) _ rfl
    | error e j₀ =>
      simp only [Result.shift_error]
      by_cases h0 : j₀ = 0
      · subst h0; simp [Nat.add_comm]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), Result.shift_error]
        congr 1; omega

/-- `p` as many times as it succeeds and consumes, collecting the values. It
stops at a failure that consumed nothing (or a success that consumed
nothing); a failure that consumed input is the result. -/
def many (p : Parser τ ε α) : Parser τ ε (List α) where
  run s i := manyGo p s i []
  run_eq s i := by
    have := manyGo_shift p s (Input.size s - (i + 0)) i 0 [] rfl
    simpa using this
  pos_le l := by
    suffices h : ∀ n i (acc : List α), l.length - i = n → i ≤ l.length →
        (manyGo p l i acc).pos ≤ l.length from h _ 0 [] rfl (Nat.zero_le _)
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i acc hn hi
      have hb := p.run_pos l i
      rw [manyGo_eq]
      cases hc : p.run l i with
      | ok a j =>
        rw [hc] at hb
        simp only [Result.pos_ok, Input.size_list] at hb
        by_cases hj : j = i
        · simp [hj, hi]
        · simp only [hj, ite_false]
          exact ih (l.length - j) (by omega) j _ rfl (by omega)
      | error e j =>
        rw [hc] at hb
        simp only [Result.pos_error, Input.size_list] at hb
        simp only
        split <;> simp <;> omega

/-- One or more. -/
def many1 (p : Parser τ ε α) : Parser τ ε (List α) := do
  let a ← p
  let as ← many p
  pure (a :: as)

/-- Zero or more `p`, separated by `sep`. After a separator an element is
required: a failure there is the result (it consumed the separator). -/
def sepBy1 (p : Parser τ ε α) (sep : Parser τ ε β) : Parser τ ε (List α) := do
  let a ← p
  let as ← many (sep *> p)
  pure (a :: as)

/-- Zero or more `p`, separated by `sep`. -/
def sepBy (p : Parser τ ε α) (sep : Parser τ ε β) : Parser τ ε (List α) :=
  sepBy1 p sep <|> pure []

/-- The longest run of tokens satisfying `f`. -/
def takeWhile [ParseError ε] (f : τ → Bool) : Parser τ ε (List τ) := many (satisfy f)

/-- Succeed, consuming nothing, if `p` fails here; fail with `unexpected`,
consuming nothing, if `p` succeeds. -/
def notFollowedBy [ParseError ε] (p : Parser τ ε α) : Parser τ ε Unit := do
  match ← optional (attempt (lookahead p)) with
  | some _ => fail ParseError.unexpected
  | none => pure ()

/-- `p` repeatedly until `stop` succeeds; the values of `p`. `stop` is consumed. -/
def manyTill [ParseError ε] (p : Parser τ ε α) (stop : Parser τ ε β) : Parser τ ε (List α) := do
  let as ← many (notFollowedBy stop *> p)
  let _ ← stop
  pure as

/-! ## Confinement -/

/-- Run `p` on exactly the next `n` tokens: `p` sees the input end after them
and must consume all of them. Fewer than `n` tokens left is `eof`; `p`
stopping short is `unexpected` where it stopped. No copying: `p` runs on a
`Slice` of the same buffer, so its positions are positions in the buffer. -/
def isolate [ParseError ε] (n : Nat) (p : Parser τ ε α) : Parser τ ε α where
  run s i :=
    if Input.size s - i < n then .error ParseError.eof i else
    match p.run (Slice.mk s (i + n)) i with
    | .ok a j => if j = i + n then .ok a j else .error ParseError.unexpected j
    | .error e j => .error e j
  run_eq s i := by
    have hL : Input.size (Input.rest s i) - 0 = Input.size s - i := by
      rw [Input.size_list, Input.length_rest, Nat.sub_zero]
    have hs : p.run (Slice.mk s (i + n)) i = (p.run (Slice.mk (Input.rest s i) n) 0).shift i := by
      rw [p.run_eq (Slice.mk s (i + n)) i, p.run_eq (Slice.mk (Input.rest s i) n) 0]
      simp [Input.rest, List.drop_take]
    show (if _ then _ else _) = Result.shift i (if _ then _ else _)
    rw [hL, hs]
    by_cases h : Input.size s - i < n
    · simp [h]
    · simp only [h, ite_false]
      cases hc : p.run (Slice.mk (Input.rest s i) n) 0 with
      | ok a j =>
        by_cases hj : j = n
        · simp [hc, hj, Nat.add_comm]
        · have : ¬ j + i = i + n := by omega
          simp [hc, hj, this]
      | error e j => simp [hc]
  pos_le l := by
    have hs : p.run (Slice.mk l (0 + n)) 0 = p.run (l.take n) 0 := by
      rw [p.run_eq]; simp
    show Result.pos (if _ then _ else _) ≤ _
    rw [hs]
    by_cases h : Input.size l - 0 < n
    · rw [ite_eq_left h]; simp
    · rw [ite_eq_right h]
      simp only [Input.size_list, Nat.sub_zero] at h
      have hb := p.pos_le (l.take n)
      rw [List.length_take] at hb
      cases hc : p.run (l.take n) 0 with
      | ok a j =>
        rw [hc] at hb; simp only [Result.pos_ok] at hb
        simp only
        split <;> simp <;> omega
      | error e j => rw [hc] at hb; simp only [Result.pos_error] at hb ⊢; omega

/-! ## Recursion -/

/-- Run `G m`, where `m` is the number of tokens left, provided `m < n`;
otherwise fail with `stuck`. The building block of `fix`. -/
def guarded [ParseError ε] (n : Nat) (G : (m : Nat) → m < n → Parser τ ε α) : Parser τ ε α where
  run s i := if h : Input.size s - i < n then (G _ h).run s i else .error ParseError.stuck i
  run_eq s i := by
    have hL : Input.size (Input.rest s i) - 0 = Input.size s - i := by
      rw [Input.size_list, Input.length_rest, Nat.sub_zero]
    have key : ∀ m m' (e : m = m') (h : m < n) (h' : m' < n), G m h = G m' h' := by
      intro m m' e h h'; subst e; rfl
    by_cases h : Input.size s - i < n
    · have h' : Input.size (Input.rest s i) - 0 < n := hL ▸ h
      show (if h : _ then _ else _) = Result.shift i (if h : _ then _ else _)
      rw [dite_eq_left h, dite_eq_left h', key _ _ hL.symm h h', (G _ h').run_eq s i]
    · have h' : ¬ Input.size (Input.rest s i) - 0 < n := hL ▸ h
      show (if h : _ then _ else _) = Result.shift i (if h : _ then _ else _)
      rw [dite_eq_right h, dite_eq_right h']; simp
  pos_le l := by
    show Result.pos (if h : _ then _ else _) ≤ _
    by_cases h : Input.size l - 0 < n
    · rw [dite_eq_left h]; exact (G _ h).pos_le l
    · rw [dite_eq_right h]; simp

/-- The recursive handle of `fix F` for a call with `n` tokens left: `fix F`
on strictly fewer tokens, `stuck` otherwise. -/
def below [ParseError ε] (F : Parser τ ε α → Parser τ ε α) (n : Nat) : Parser τ ε α :=
  guarded n fun m _ => F (below F m)
termination_by n

/-- The parser defined by the recursive equation `p = F p`. Inside `F`, the
argument may be used after consuming input (an array element after `[`, a
nested block after its opening tag): that is a call on fewer tokens, and it
runs `fix F`. A call without progress fails with `stuck`. Total by
well-founded recursion on the tokens left; no fuel. -/
def fix [ParseError ε] (F : Parser τ ε α → Parser τ ε α) : Parser τ ε α where
  run s i := (F (below F (Input.size s - i))).run s i
  run_eq s i := by
    have hL : Input.size (Input.rest s i) - 0 = Input.size s - i := by
      rw [Input.size_list, Input.length_rest, Nat.sub_zero]
    simp only [hL]; exact (F _).run_eq s i
  pos_le l := (F _).pos_le l

/-- Fail with `e` as a failure that consumed: reported one token on (or where
it stands, at the end of input), so no alternative takes over. -/
def failAhead (e : ε) : Parser τ ε α where
  run s i :=
    match Input.get? s i with
    | some _ => .error e (i + 1)
    | none => .error e i
  run_eq s i := by
    have h := Input.get?_rest s i 0
    simp only [Nat.add_zero] at h
    simp only [Input.get?_list, h]
    cases Input.get? s i <;> simp [Nat.add_comm]
  pos_le l := by cases l <;> simp

/-- **The depth-bounded fixpoint**: `fix F`, with at most `max` recursive
calls active at once. A call past the bound fails with
`ParseError.depthExceeded`, as a failure that consumed (`failAhead`: reported
one token past the call, inside the over-deep construct), so that no
alternative such as `sepBy`'s empty case can swallow it and the whole parse
fails with that error. The recursion is structural on `max`, so the
native stack depth is bounded whatever the input: this is the form to use on
untrusted input. As in `fix`, the handle runs only on strictly fewer tokens. -/
def fixDepth [ParseError ε] (max : Nat) (F : Parser τ ε α → Parser τ ε α) : Parser τ ε α :=
  match max with
  | 0 => failAhead ParseError.depthExceeded
  | d + 1 =>
    { run := fun s i => (F (guarded (Input.size s - i) fun _ _ => fixDepth d F)).run s i
      run_eq := fun s i => by
        have hL : Input.size (Input.rest s i) - 0 = Input.size s - i := by
          rw [Input.size_list, Input.length_rest, Nat.sub_zero]
        show (F (guarded (Input.size s - i) fun _ _ => fixDepth d F)).run s i =
          Result.shift i ((F (guarded (Input.size (Input.rest s i) - 0) fun _ _ => fixDepth d F)).run
            (Input.rest s i) 0)
        rw [hL]; exact (F _).run_eq s i
      pos_le := fun l => (F _).pos_le l }

end Parser

end Keel
