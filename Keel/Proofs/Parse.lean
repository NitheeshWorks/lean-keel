import Keel.RepoImpl.Parse

/-!
# Proofs: the laws of `Keel.Parse`, on lists

Every combinator gets one equation for `Parser.parse`, its meaning on a list
of tokens. Two parsers with the same list meaning are equal (`Parser.ext`),
and a parser run on any buffer is determined by its list meaning
(`run_eq_of_parse`), so these equations are the whole story.
-/

namespace Keel

namespace Parser

variable {τ ε ε' α β : Type}

/-! ## The bridge between buffers and lists -/

/-- Running at position `j` of a list is parsing the list from `j` on. -/
theorem run_toReply (p : Parser τ ε α) (l : List τ) (j : Nat) :
    (p.run l j).toReply l = p.parse (l.drop j) := by
  rw [p.run_list l j, Result.toReply_shift]; rfl

/-- What a parser reports on a list determines its result there. -/
theorem run_zero_of_parse {p q : Parser τ ε α} {l : List τ} (h : p.parse l = q.parse l) :
    p.run l 0 = q.run l 0 := by
  have hp := p.pos_le l
  have hq := q.pos_le l
  unfold parse at h
  cases hc : p.run l 0 <;> cases hd : q.run l 0 <;> rw [hc, hd] at h <;>
    simp only [Result.toReply_ok, Result.toReply_error, Reply.ok.injEq, Reply.error.injEq,
      reduceCtorEq] at h <;> rw [hc] at hp <;> rw [hd] at hq <;>
    simp only [Result.pos_ok, Result.pos_error] at hp hq
  all_goals
    obtain ⟨rfl, h2⟩ := h
    have := congrArg List.length h2
    simp only [List.length_drop] at this
    congr 1; omega

/-- **Extensionality.** Parsers with the same meaning on every list are
equal: the buffer and the position add nothing. -/
theorem ext {p q : Parser τ ε α} (h : ∀ l, p.parse l = q.parse l) : p = q := by
  have hrun : ∀ {σ : Type} [Input σ τ] (s : σ) (i : Nat), p.run s i = q.run s i := by
    intro σ _ s i
    rw [p.run_eq, q.run_eq, run_zero_of_parse (h _)]
  cases p with
  | mk prun _ _ =>
    cases q with
    | mk qrun _ _ =>
      have : @prun = @qrun := by
        funext σ inst s i
        exact hrun s i
      subst this; rfl

/-- The result on any buffer, from the meaning on the tokens left. -/
theorem run_eq_of_parse {σ : Type} [Input σ τ] (p : Parser τ ε α) {s : σ} {i : Nat} {a : α}
    {r : List τ} (h : p.parse (Input.rest s i) = .ok a r) (hi : i ≤ Input.size s) :
    p.run s i = .ok a (Input.size s - r.length) := by
  rw [p.run_eq s i]
  have hb := p.pos_le (Input.rest s i)
  unfold parse at h
  cases hc : p.run (Input.rest s i) 0 with
  | ok a' j =>
    rw [hc] at h hb
    simp only [Result.toReply_ok, Reply.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Result.pos_ok, Input.length_rest] at hb
    simp only [Result.shift_ok, Result.ok.injEq, true_and, List.length_drop]
    rw [Input.size_eq] at hb hi ⊢
    omega
  | error e j => rw [hc] at h; simp at h

/-- The error on any buffer, from the meaning on the tokens left. -/
theorem run_eq_error_of_parse {σ : Type} [Input σ τ] (p : Parser τ ε α) {s : σ} {i : Nat} {e : ε}
    {r : List τ} (h : p.parse (Input.rest s i) = .error e r) (hi : i ≤ Input.size s) :
    p.run s i = .error e (Input.size s - r.length) := by
  rw [p.run_eq s i]
  have hb := p.pos_le (Input.rest s i)
  unfold parse at h
  cases hc : p.run (Input.rest s i) 0 with
  | ok a' j => rw [hc] at h; simp at h
  | error e' j =>
    rw [hc] at h hb
    simp only [Result.toReply_error, Reply.error.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Result.pos_error, Input.length_rest] at hb
    simp only [Result.shift_error, Result.error.injEq, true_and, List.length_drop]
    rw [Input.size_eq] at hb hi ⊢
    omega

/-- A result on a buffer is the list meaning on the tokens from the start position. -/
theorem parse_of_run {σ : Type} [Input σ τ] (p : Parser τ ε α) {s : σ} {i : Nat} {a : α} {j : Nat}
    (h : p.run s i = .ok a j) : p.parse (Input.rest s i) = .ok a (Input.rest s j) := by
  rw [p.run_eq s i] at h
  unfold parse
  cases hc : p.run (Input.rest s i) 0 with
  | ok a' j' =>
    rw [hc] at h
    simp only [Result.shift_ok, Result.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Input.rest, List.drop_drop, Nat.add_comm]
  | error e j' => rw [hc] at h; simp at h

/-- What is left is a suffix of the input. -/
theorem parse_rest_suffix (p : Parser τ ε α) (l : List τ) : (p.parse l).rest <:+ l := by
  unfold parse
  cases p.run l 0 <;> exact List.drop_suffix _ _

/-! ## The monad -/

@[simp] theorem parse_pure (a : α) (l : List τ) : (pure a : Parser τ ε α).parse l = .ok a l := by
  show (Result.ok a 0).toReply l = _
  simp

@[simp] theorem parse_bind (p : Parser τ ε α) (f : α → Parser τ ε β) (l : List τ) :
    (p >>= f).parse l = (p.parse l).bind fun a r => (f a).parse r := by
  show ((Parser.bind p f).run l 0).toReply l = (p.parse l).bind _
  unfold parse
  simp only [Parser.bind]
  cases p.run l 0 with
  | ok a j => simp [run_toReply]
  | error e j => rfl

instance : LawfulMonad (Parser τ ε) := LawfulMonad.mk'
  (id_map := fun p => ext fun l => by
    show (p >>= fun a => pure (id a)).parse l = p.parse l
    rw [parse_bind]; cases p.parse l <;> simp)
  (pure_bind := fun a f => ext fun l => by rw [parse_bind]; simp)
  (bind_assoc := fun p f g => ext fun l => by
    simp only [parse_bind]; cases p.parse l <;> simp)

@[simp] theorem parse_map (f : α → β) (p : Parser τ ε α) (l : List τ) :
    (f <$> p).parse l = (p.parse l).map f := by
  rw [← bind_pure_comp, parse_bind]; cases p.parse l <;> simp

@[simp] theorem parse_seqRight (p : Parser τ ε α) (q : Parser τ ε β) (l : List τ) :
    (p *> q).parse l = (p.parse l).bind fun _ r => q.parse r := by
  rw [seqRight_eq_bind, parse_bind]

@[simp] theorem parse_seqLeft (p : Parser τ ε α) (q : Parser τ ε β) (l : List τ) :
    (p <* q).parse l = (p.parse l).bind fun a r => (q.parse r).map fun _ => a := by
  rw [seqLeft_eq_bind, parse_bind]
  cases p.parse l <;> simp

/-! ## Failure and choice -/

@[simp] theorem parse_fail (e : ε) (l : List τ) : (fail e : Parser τ ε α).parse l = .error e l := by
  show (Result.error e 0).toReply l = _
  simp

/-- **Committed choice.** `q` runs only when `p` failed with nothing consumed. -/
theorem parse_orElse (p q : Parser τ ε α) (l : List τ) :
    (p <|> q).parse l =
      match p.parse l with
      | .ok a r => .ok a r
      | .error e r => if r.length = l.length then q.parse l else .error e r := by
  show ((Parser.orElse p fun _ => q).run l 0).toReply l = _
  have hb := p.pos_le l
  unfold parse
  simp only [Parser.orElse]
  cases hc : p.run l 0 with
  | ok a j => rfl
  | error e j =>
    rw [hc] at hb
    simp only [Result.pos_error] at hb
    by_cases hj : j = 0
    · simp [hj]
    · have : ¬ l.length - j = l.length := by omega
      simp [hj, this]

@[simp] theorem parse_attempt (p : Parser τ ε α) (l : List τ) :
    (attempt p).parse l =
      match p.parse l with
      | .ok a r => .ok a r
      | .error e _ => .error e l := by
  unfold parse attempt
  cases hc : p.run l 0 <;> simp [hc]

@[simp] theorem parse_lookahead (p : Parser τ ε α) (l : List τ) :
    (lookahead p).parse l =
      match p.parse l with
      | .ok a _ => .ok a l
      | .error e r => .error e r := by
  unfold parse lookahead
  cases hc : p.run l 0 <;> simp [hc]

@[simp] theorem parse_mapError (f : ε → ε') (p : Parser τ ε α) (l : List τ) :
    (p.mapError f).parse l =
      match p.parse l with
      | .ok a r => .ok a r
      | .error e r => .error (f e) r := by
  unfold parse mapError
  cases hc : p.run l 0 <;> simp [hc]

@[simp] theorem parse_withError (e : ε) (p : Parser τ ε α) (l : List τ) :
    (p <?> e).parse l =
      match p.parse l with
      | .ok a r => .ok a r
      | .error _ r => .error e r := by
  show (p.mapError _).parse l = _
  rw [parse_mapError]

/-- `optional p` is `some` of a success, `none` (nothing consumed) for a
failure without consumption, and the error of a failure that consumed. -/
theorem parse_optional (p : Parser τ ε α) (l : List τ) :
    (optional p).parse l =
      match p.parse l with
      | .ok a r => .ok (some a) r
      | .error e r => if r.length = l.length then .ok none l else .error e r := by
  unfold optional
  rw [parse_orElse, parse_map]
  cases p.parse l <;> simp

/-! ## Tokens -/

@[simp] theorem parse_peek? (l : List τ) : (peek? : Parser τ ε (Option τ)).parse l = .ok l.head? l := by
  show (Result.ok _ 0).toReply l = _
  cases l <;> simp

@[simp] theorem parse_next?_nil : (next? : Parser τ ε (Option τ)).parse [] = .ok none [] := rfl

@[simp] theorem parse_next?_cons (t : τ) (l : List τ) :
    (next? : Parser τ ε (Option τ)).parse (t :: l) = .ok (some t) l := rfl

@[simp] theorem parse_satisfy_nil [ParseError ε] (f : τ → Bool) :
    (satisfy f : Parser τ ε τ).parse [] = .error ParseError.eof [] := rfl

@[simp] theorem parse_satisfy_cons [ParseError ε] (f : τ → Bool) (t : τ) (l : List τ) :
    (satisfy f : Parser τ ε τ).parse (t :: l) =
      if f t then .ok t l else .error ParseError.unexpected (t :: l) := by
  show (if f t then Result.ok t (0 + 1) else Result.error ParseError.unexpected 0).toReply (t :: l) = _
  by_cases h : f t <;> simp [h]

@[simp] theorem parse_next_nil [ParseError ε] : (next : Parser τ ε τ).parse [] = .error ParseError.eof [] :=
  parse_satisfy_nil _

@[simp] theorem parse_next_cons [ParseError ε] (t : τ) (l : List τ) :
    (next : Parser τ ε τ).parse (t :: l) = .ok t l := by
  simp [next]

@[simp] theorem parse_token_nil [ParseError ε] [DecidableEq τ] (t : τ) :
    (token t : Parser τ ε τ).parse [] = .error ParseError.eof [] := parse_satisfy_nil _

@[simp] theorem parse_token_cons [ParseError ε] [DecidableEq τ] (t u : τ) (l : List τ) :
    (token t : Parser τ ε τ).parse (u :: l) =
      if u = t then .ok u l else .error ParseError.unexpected (u :: l) := by
  simp [token]

@[simp] theorem parse_eof_nil [ParseError ε] : (eof : Parser τ ε Unit).parse [] = .ok () [] := by
  simp [eof]

@[simp] theorem parse_eof_cons [ParseError ε] (t : τ) (l : List τ) :
    (eof : Parser τ ε Unit).parse (t :: l) = .error ParseError.unexpected (t :: l) := by
  simp [eof]

private theorem parse_tokens [ParseError ε] [DecidableEq τ] (l r : List τ) :
    (tokens l : Parser τ ε Unit).parse (l ++ r) = .ok () r := by
  induction l with
  | nil => simp [tokens]
  | cons t l ih => simp [tokens, ih]

private theorem parse_tokens_ok [ParseError ε] [DecidableEq τ] (l x r : List τ) :
    (tokens l : Parser τ ε Unit).parse x = .ok () r → x = l ++ r := by
  induction l generalizing x with
  | nil => simp [tokens]
  | cons t l ih =>
    cases x with
    | nil => simp [tokens]
    | cons u x =>
      by_cases h : u = t
      · subst h; simpa [tokens] using ih x
      · simp [tokens, h]

/-- **Literals.** `lit l` reads exactly `l`, on any continuation. -/
@[simp] theorem parse_lit [ParseError ε] [DecidableEq τ] (l r : List τ) :
    (lit l : Parser τ ε Unit).parse (l ++ r) = .ok () r := by
  simp [lit, parse_tokens]

/-- `lit l` succeeds only on inputs that start with `l`. -/
theorem parse_lit_ok [ParseError ε] [DecidableEq τ] {l x r : List τ} :
    (lit l : Parser τ ε Unit).parse x = .ok () r ↔ x = l ++ r := by
  constructor
  · intro h
    simp only [lit, parse_attempt] at h
    split at h
    · rename_i r' hr; cases h; exact parse_tokens_ok l x r hr
    · cases h
  · rintro rfl; exact parse_lit l r

/-- A failed `lit` consumes nothing. -/
theorem parse_lit_error [ParseError ε] [DecidableEq τ] {l x r : List τ} {e : ε}
    (h : (lit l : Parser τ ε Unit).parse x = .error e r) : r = x := by
  simp only [lit, parse_attempt] at h
  split at h <;> cases h; rfl

/-- **Lookahead for a literal.** -/
@[simp] theorem parse_startsWith [ParseError ε] [DecidableEq τ] (l x : List τ) :
    (startsWith l : Parser τ ε Bool).parse x = .ok (decide (l <+: x)) x := by
  unfold startsWith
  rw [parse_orElse]
  by_cases h : l <+: x
  · obtain ⟨r, rfl⟩ := h
    simp [List.prefix_append]
  · cases hc : (lit l : Parser τ ε Unit).parse x with
    | ok u r =>
      exact absurd ⟨r, ((parse_lit_ok).1 hc).symm⟩ h
    | error e r =>
      have := parse_lit_error hc; subst this
      simp [hc, h]

@[simp] theorem parse_take_zero [ParseError ε] (l : List τ) :
    (take 0 : Parser τ ε (List τ)).parse l = .ok [] l := by
  simp [take]

/-- `take n` reads `n` tokens when there are that many. -/
theorem parse_take [ParseError ε] (n : Nat) (l r : List τ) (h : l.length = n) :
    (take n : Parser τ ε (List τ)).parse (l ++ r) = .ok l r := by
  induction n generalizing l with
  | zero => cases l <;> simp_all
  | succ n ih =>
    cases l with
    | nil => simp at h
    | cons t l => simp [take, ih l (by simpa using h)]

/-! ## Repetition -/

private theorem manyGo_acc (p : Parser τ ε α) (l : List τ) :
    ∀ (n i : Nat) (acc : List α), l.length - i = n →
      manyGo p l i acc = (manyGo p l i []).map (acc.reverse ++ ·) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i acc hn
    have hb := p.run_pos l i
    rw [manyGo_eq, manyGo_eq (acc := [])]
    cases hc : p.run l i with
    | ok a j =>
      rw [hc] at hb
      simp only [Result.pos_ok, Input.size_list] at hb
      by_cases hj : j = i
      · simp [hj]
      · simp only [hj, ite_false]
        rw [ih (l.length - j) (by omega) j (a :: acc) rfl,
          ih (l.length - j) (by omega) j [a] rfl, Result.map_map]
        congr 1; funext x; simp
    | error e j => by_cases hj : j = i <;> simp [hj]

/-- **Repetition.** `many p` unfolds once: a step that consumed continues the
loop on what it left; a step that consumed nothing ends it. -/
theorem parse_many (p : Parser τ ε α) (l : List τ) :
    (many p).parse l =
      match p.parse l with
      | .ok a r => if r.length = l.length then .ok [] l else ((many p).parse r).map (a :: ·)
      | .error e r => if r.length = l.length then .ok [] l else .error e r := by
  have hb := p.pos_le l
  show (manyGo p l 0 []).toReply l = _
  unfold parse
  rw [manyGo_eq]
  cases hc : p.run l 0 with
  | ok a j =>
    rw [hc] at hb
    simp only [Result.pos_ok] at hb
    by_cases hj : j = 0
    · simp [hj]
    · have : ¬ l.length - j = l.length := by omega
      simp only [hj, ite_false, Result.toReply_ok, List.length_drop, this]
      rw [manyGo_acc p l _ j [a] rfl, Result.toReply_map]
      have hs := manyGo_shift p l (l.length - (j + 0)) j 0 [] rfl
      simp only [Nat.add_zero] at hs
      rw [hs, Result.toReply_shift]
      rfl
  | error e j =>
    rw [hc] at hb
    simp only [Result.pos_error] at hb
    by_cases hj : j = 0
    · simp [hj]
    · have : ¬ l.length - j = l.length := by omega
      simp [hj, this]

/-- `many p` on a list whose every step is a consuming success followed by a
non-consuming failure (or the end) collects the values. Stated as a fold:
the steps are given by their values and leftovers. -/
theorem parse_many_nil_of_error (p : Parser τ ε α) (l : List τ) (e : ε)
    (h : p.parse l = .error e l) : (many p).parse l = .ok [] l := by
  rw [parse_many, h]; simp

theorem parse_many_cons (p : Parser τ ε α) {l r : List τ} {a : α} (h : p.parse l = .ok a r)
    (hr : r.length < l.length) : (many p).parse l = ((many p).parse r).map (a :: ·) := by
  rw [parse_many, h]; simp [Nat.ne_of_lt hr]

/-- **`takeWhile`** reads the longest prefix of tokens satisfying `f`. -/
@[simp] theorem parse_takeWhile [ParseError ε] (f : τ → Bool) (l : List τ) :
    (takeWhile f : Parser τ ε (List τ)).parse l = .ok (l.takeWhile f) (l.dropWhile f) := by
  induction l with
  | nil => simp [takeWhile, parse_many]
  | cons t l ih =>
    unfold takeWhile at ih ⊢
    by_cases h : f t
    · rw [parse_many_cons (a := t) (r := l) _ (by simp [h]) (by simp), ih]; simp [h]
    · rw [parse_many]; simp [h]

theorem parse_many1 (p : Parser τ ε α) (l : List τ) :
    (many1 p).parse l = (p.parse l).bind fun a r => ((many p).parse r).map (a :: ·) := by
  simp only [many1, parse_bind]
  cases p.parse l with
  | ok a r => simp only [Reply.bind_ok]; cases (many p).parse r <;> simp
  | error e r => rfl

theorem parse_sepBy1 (p : Parser τ ε α) (sep : Parser τ ε β) (l : List τ) :
    (sepBy1 p sep).parse l = (p.parse l).bind fun a r => ((many (sep *> p)).parse r).map (a :: ·) := by
  simp only [sepBy1, parse_bind]
  cases p.parse l with
  | ok a r => simp only [Reply.bind_ok]; cases (many (sep *> p)).parse r <;> simp
  | error e r => rfl

@[simp] theorem parse_notFollowedBy [ParseError ε] (p : Parser τ ε α) (l : List τ) :
    (notFollowedBy p).parse l =
      match p.parse l with
      | .ok _ _ => .error ParseError.unexpected l
      | .error _ _ => .ok () l := by
  simp only [notFollowedBy, parse_bind, parse_optional, parse_attempt, parse_lookahead]
  cases p.parse l <;> simp

/-! ## Confinement -/

/-- **Confinement.** `isolate n p` parses the next `n` tokens with `p`, which
must consume all of them, and leaves the rest untouched. -/
theorem parse_isolate [ParseError ε] (n : Nat) (p : Parser τ ε α) (l : List τ) :
    (isolate n p).parse l =
      if l.length < n then .error ParseError.eof l else
      match p.parse (l.take n) with
      | .ok a r => if r = [] then .ok a (l.drop n) else .error ParseError.unexpected (r ++ l.drop n)
      | .error e r => .error e (r ++ l.drop n) := by
  have hs : p.run (Slice.mk l (0 + n)) 0 = p.run (l.take n) 0 := by
    rw [p.run_eq]; simp
  unfold parse
  show Result.toReply l (if _ then _ else _) = _
  rw [hs]
  by_cases h : l.length < n
  · rw [ite_eq_left (by simpa using h), ite_eq_left h]; simp
  · rw [ite_eq_right (by simpa using h), ite_eq_right h]
    have hb := p.pos_le (l.take n)
    rw [List.length_take] at hb
    have hsplit : ∀ j, j ≤ n → l.drop j = (l.take n).drop j ++ l.drop n := by
      intro j hj
      conv => lhs; rw [← List.take_append_drop n l]
      rw [List.drop_append_of_le_length (by simp; omega)]
    cases hc : p.run (l.take n) 0 with
    | ok a j =>
      rw [hc] at hb; simp only [Result.pos_ok] at hb
      have hj : j ≤ n := by omega
      simp only [Result.toReply_ok]
      by_cases hjn : j = n
      · have hnil : (l.take n).drop j = [] := by simp; omega
        rw [ite_eq_left hnil, ite_eq_left (by omega : j = 0 + n), hjn]; rfl
      · have hne : (l.take n).drop j ≠ [] := by simp; omega
        rw [ite_eq_right hne, ite_eq_right (by omega : ¬ j = 0 + n), Result.toReply_error, hsplit j hj]
    | error e j =>
      rw [hc] at hb; simp only [Result.pos_error] at hb
      simp only [Result.toReply_error, hsplit j (by omega)]

/-- `isolate n p` on exactly `n` tokens that `p` reads completely. -/
theorem parse_isolate_append [ParseError ε] {n : Nat} {p : Parser τ ε α} {l r : List τ} {a : α}
    (hl : l.length = n) (hp : p.parse l = .ok a []) : (isolate n p).parse (l ++ r) = .ok a r := by
  rw [parse_isolate]
  subst hl
  simp [hp]

/-! ## Recursion -/

/-- **Fixpoint, unfolded.** `fix F` is `F` applied to the handle for the
current length. -/
theorem parse_fix [ParseError ε] (F : Parser τ ε α → Parser τ ε α) (l : List τ) :
    (fix F).parse l = (F (below F l.length)).parse l := by
  show ((F (below F (l.length - 0))).run l 0).toReply l = _
  rw [Nat.sub_zero]; rfl

/-- **The recursive handle.** On fewer tokens than the call that made it, the
handle is the fixpoint; otherwise it reports `stuck`. -/
theorem parse_below [ParseError ε] (F : Parser τ ε α → Parser τ ε α) (n : Nat) (l : List τ) :
    (below F n).parse l = if l.length < n then (fix F).parse l else .error ParseError.stuck l := by
  rw [below]
  show (Result.toReply l (if h : l.length - 0 < n then _ else _)) = _
  by_cases h : l.length < n
  · rw [dite_eq_left (by simpa using h), ite_eq_left h, parse_fix]; rfl
  · rw [dite_eq_right (by simpa using h), ite_eq_right h]; simp

theorem parse_below_of_lt [ParseError ε] (F : Parser τ ε α → Parser τ ε α) {n : Nat} {l : List τ}
    (h : l.length < n) : (below F n).parse l = (fix F).parse l := by
  rw [parse_below, ite_eq_left h]

theorem parse_guarded [ParseError ε] (n : Nat) (G : (m : Nat) → m < n → Parser τ ε α) (l : List τ) :
    (guarded n G).parse l = if h : l.length < n then (G _ h).parse l else .error ParseError.stuck l := by
  show Result.toReply l (if h : l.length - 0 < n then _ else _) = _
  by_cases h : l.length < n
  · rw [dite_eq_left (by simpa using h), dite_eq_left h]
    have : (G (Input.size l - 0) (by simpa using h)) = G l.length h := by
      congr 1
    rw [this]; rfl
  · rw [dite_eq_right (by simpa using h), dite_eq_right h]; simp

@[simp] theorem parse_failAhead (e : ε) (l : List τ) :
    (failAhead e : Parser τ ε α).parse l = .error e l.tail := by
  cases l <;> rfl

/-- **Past the bound**: no nested call is left, so the parser fails with
`depthExceeded`, as a failure that consumed (one token, if there is one). -/
@[simp] theorem parse_fixDepth_zero [ParseError ε] (F : Parser τ ε α → Parser τ ε α) (l : List τ) :
    (fixDepth 0 F).parse l = .error ParseError.depthExceeded l.tail := by
  simp [fixDepth]

/-- **One level**: `fixDepth (d + 1) F` is `F` applied to a handle that runs
`fixDepth d F` on strictly fewer tokens. -/
theorem parse_fixDepth_succ [ParseError ε] (d : Nat) (F : Parser τ ε α → Parser τ ε α) (l : List τ) :
    (fixDepth (d + 1) F).parse l = (F (guarded l.length fun _ _ => fixDepth d F)).parse l := by
  show ((F (guarded (l.length - 0) fun _ _ => fixDepth d F)).run l 0).toReply l = _
  rw [Nat.sub_zero]; rfl

/-- **The bound is the only difference**: with more depth than tokens (every
nested call consumes, so no input nests deeper than its length), the bounded
fixpoint is the unbounded one. -/
theorem fixDepth_eq_fix [ParseError ε] (F : Parser τ ε α → Parser τ ε α) :
    ∀ (d : Nat) (l : List τ), l.length < d → (fixDepth d F).parse l = (fix F).parse l
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | d + 1, l, h => by
    rw [parse_fixDepth_succ, parse_fix]
    have hhandle : (guarded l.length fun _ _ => fixDepth d F) = below F l.length := by
      apply ext
      intro l'
      rw [parse_guarded, parse_below]
      by_cases h' : l'.length < l.length
      · rw [dite_eq_left h', ite_eq_left h']
        exact fixDepth_eq_fix F d l' (by omega)
      · rw [dite_eq_right h', ite_eq_right h']
    rw [hhandle]

end Parser

end Keel
