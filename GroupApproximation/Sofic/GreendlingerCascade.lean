import GroupApproximation.Sofic.GreendlingerChunks

/-!
# The cascade: where the leading block finally stops

`GreendlingerThreeFactor` reduces the gate to `TailSubwordBeyondBlock` --- the
subword the rest of the product carries lies beyond the block the leading factor
destroys --- and records that `LeadingConfinement`, the statement that the block
stops inside the *next* factor's palindrome, is very likely false.  Its header
carries a configuration satisfying every constraint the six weight moves and
`C'(1/6)` impose while the block runs `21` letters past what the second factor
keeps, and observes that the conclusion still holds there for a reason the
descent never looks at: **the third factor's rotation is untouched, and sits in
the word exactly where the block stops.**

This file makes that observation into the frame the descent runs in.

## The cascade

The reduced word of an expression loses a prefix at every stage:

  `exists_residual_step` --- `W(x :: e) = A ++ W(e).drop N`,

with `A` the surviving part of the leading factor and `N` the block it lost.
Iterating and composing the two drops gives

  `exists_cascade` --- `W(e) = A ++ W(e.drop k).drop N` for **every** `k`,

so the word of any suffix of the expression is visible in the word of the whole,
shifted by one number.  Both are unconditional: no minimality, no small
cancellation, no palindromes.  This is the arc data the count needs, in the only
form the descent can consume, and it is sharper than a matching: the chunks of a
product of reduced words are already known to be infixes in order
(`GreendlingerChunks.exists_chunk_decomposition`), and what the cascade adds is
that the *residual* word of each suffix is one of those infixes' contexts.

## Landing

`GreendlingerAt.transport` carries a located subword across a cascade step: a
subword of `W(e.drop k)` beginning at or after the drop `N` reappears in `W(e)`
at position `|A| + n - N`.  So the descent no longer has to hand the block to
the factor next to it.  It has to hand it to **whichever factor it stops in**,
and the only thing it must know is that it stops within a sixth of a rotation
past that factor's conjugator:

  `LandsIn R b V m` --- the word `V` is `A ++ W(f').drop N` for a strictly
  shorter minimal expression `f'` in palindromic normal form, with
  `b + N ≤ |A| + |c'| + i` and `6i < |t'|`, where `b` is the block's length.

`landsIn_of_confined` is the case that needs no jump at all: when the block stops
inside the next factor's own conjugator, `A = []` and `N = 0` and the landing
data is the tail itself.  That is exactly the two inheritance cases of
`GreendlingerThreeFactor`'s descent, so `LandsIn` is a weakening of what the
descent already proves --- and, unlike `LeadingConfinement`, it is **not
refuted** by the configuration in that file's header: there the block stops
inside `c₃`, so `N ≤ |c₃|` and `i = 0` serve.

## What is left

`CascadeLanding`, and only it.  The descent below is complete: it splits the
leading cancellation into the free case, the case that keeps enough of the
leading rotation, and the case that hands the block on, and the third case is
the hypothesis.  Nothing else is assumed --- in particular the swallow bound is
part of the hypothesis rather than a separate appeal to confinement, which is
what let `swallow_bound_of_minimal` be dropped from the route.

Unconditional except where `CascadeLanding` is named.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Dropping twice -/

/-- Dropping `n` then `m` letters is dropping `n + m`. -/
theorem drop_add {β : Type*} :
    ∀ (n m : ℕ) (l : List β), l.drop (n + m) = (l.drop n).drop m := by
  intro n
  induction n with
  | zero =>
      intro m l
      rw [Nat.zero_add, List.drop_zero]
  | succ n ih =>
      intro m l
      cases l with
      | nil => rw [List.drop_nil, List.drop_nil, List.drop_nil]
      | cons a l₁ =>
          rw [show n + 1 + m = (n + m) + 1 from by omega, List.drop_succ_cons,
            List.drop_succ_cons, ih m l₁]

/-! ## The residual word loses a prefix at every stage -/

/-- **One stage of the cascade.**  The reduced word of an expression is the
surviving part of its leading factor followed by the reduced word of the rest
with a prefix removed.

Unconditional: it is the cancellation decomposition of two reduced words, read
with the leading factor on the left. -/
theorem exists_residual_step [DecidableEq α]
    (x : FreeGroup α × List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) :
    ∃ (A : List (α × Bool)) (N : ℕ),
      (conjEval (x :: e)).toWord = A ++ (conjEval e).toWord.drop N := by
  obtain ⟨A', M, B', _h1, h2, h3, h4⟩ :=
    exists_cancellation_decomposition (conjEval e).toWord
      FreeGroup.isReduced_toWord (x.1 * FreeGroup.mk x.2 * x.1⁻¹).toWord
      FreeGroup.isReduced_toWord
  refine ⟨A', M.length, ?_⟩
  have hdrop : (conjEval e).toWord.drop M.length = B' := by
    rw [h2, drop_append_of_ge (FreeGroup.invRev M) M.length B'
      (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
      Nat.sub_self, List.drop_zero]
  have heval : conjEval (x :: e) = FreeGroup.mk (A' ++ B') := by
    rw [conjEval_cons', ← h4, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
  rw [hdrop, heval, FreeGroup.toWord_mk, h3.reduce_eq]

/-- **The cascade.**  The reduced word of an expression contains the reduced
word of *every* suffix of the expression, with a prefix removed: one surviving
block `A` at the front and one number `N` measuring everything the factors
before it destroyed.

This is what lets the descent hand its block to a factor it is not adjacent to.
Unconditional. -/
theorem exists_cascade [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))),
      ∃ (A : List (α × Bool)) (N : ℕ),
        (conjEval e).toWord = A ++ (conjEval (e.drop k)).toWord.drop N := by
  intro k
  induction k with
  | zero =>
      intro e
      exact ⟨[], 0, by rw [List.drop_zero, List.drop_zero, List.nil_append]⟩
  | succ k ih =>
      intro e
      cases e with
      | nil =>
          exact ⟨[], 0, by rw [List.drop_nil, List.drop_zero, List.nil_append]⟩
      | cons x e' =>
          obtain ⟨A₀, N₀, h₀⟩ := exists_residual_step x e'
          obtain ⟨A₁, N₁, h₁⟩ := ih e'
          rw [List.drop_succ_cons]
          rcases le_or_gt N₀ A₁.length with hle | hgt
          · refine ⟨A₀ ++ A₁.drop N₀, N₁, ?_⟩
            rw [h₀, h₁, drop_append_of_le N₀ A₁ _ hle, List.append_assoc]
          · refine ⟨A₀, N₁ + (N₀ - A₁.length), ?_⟩
            rw [h₀, h₁, drop_append_of_ge A₁ N₀ _ (by omega), drop_add]

/-! ## Carrying a located subword across a cascade step -/

/-- **Transport.**  A subword located at or after the drop survives the drop,
and lands `N` letters earlier inside whatever precedes it.

This is the whole of what the cascade is for: it replaces
`GreendlingerThreeFactor.greendlingerAt_inherit`'s single-factor step by a step
across any number of factors at once. -/
theorem GreendlingerAt.transport {R : Set (List (α × Bool))}
    {V : List (α × Bool)} {n N : ℕ} (h : GreendlingerAt R n V)
    (A : List (α × Bool)) (hN : N ≤ n) :
    GreendlingerAt R (A.length + (n - N)) (A ++ V.drop N) := by
  obtain ⟨X, u, C, hV, hXlen, s, hs, hupre, hlt⟩ := h
  refine ⟨A ++ X.drop N, u, C, ?_, ?_, s, hs, hupre, hlt⟩
  · rw [hV, drop_append_of_le N X (u ++ C) (by omega)]
    simp only [List.append_assoc]
  · rw [List.length_append, List.length_drop]
    omega

/-! ## The landing site -/

/-- **The block lands in a later factor's conjugator.**  The word `V` --- what
the rest of the product spells --- is read as `A ++ W.drop N` for the reduced
word `W` of a strictly shorter minimal expression whose leading factor is in
palindromic normal form `(c', t')`, and the block `M` stops no more than `i`
letters into that factor's rotation, for `i` below a sixth of it.

`m` is the length the landing expression has to beat, which is what makes the
descent below terminate. -/
def LandsIn [DecidableEq α] (R : Set (List (α × Bool)))
    (b : ℕ) (V : List (α × Bool)) (m : ℕ) : Prop :=
  ∃ (c' t' : List (α × Bool)) (f : List (FreeGroup α × List (α × Bool)))
    (A : List (α × Bool)) (N i : ℕ),
    f.length < m ∧
    V = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N ∧
    t' ∈ symmetrization R ∧
    FreeGroup.IsReduced (palindrome c' t') ∧
    IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)) ∧
    6 * i < t'.length ∧ N ≤ c'.length + i ∧
    b + N ≤ A.length + c'.length + i

/-- A landing site for a block serves for any shorter block. -/
theorem LandsIn.of_le [DecidableEq α] {R : Set (List (α × Bool))}
    {b b' : ℕ} {V : List (α × Bool)} {m : ℕ} (h : LandsIn R b V m)
    (hle : b' ≤ b) : LandsIn R b' V m := by
  obtain ⟨c', t', f, A, N, i, hf, hV, ht', hredp', hmin, hi, hN, hM⟩ := h
  exact ⟨c', t', f, A, N, i, hf, hV, ht', hredp', hmin, hi, hN, by omega⟩

/-- A landing site found among fewer factors serves among more. -/
theorem LandsIn.mono [DecidableEq α] {R : Set (List (α × Bool))}
    {b : ℕ} {V : List (α × Bool)} {m m' : ℕ} (h : LandsIn R b V m)
    (hm : m ≤ m') : LandsIn R b V m' := by
  obtain ⟨c', t', f, A, N, i, hf, hV, ht', hredp', hmin, hi, hN, hM⟩ := h
  exact ⟨c', t', f, A, N, i, by omega, hV, ht', hredp', hmin, hi, hN, hM⟩

/-- **The case that needs no jump.**  When the block stops inside the next
factor's own conjugator --- or at most a sixth of a rotation past it --- the
tail itself is the landing site, with nothing dropped and nothing surviving in
front.

These are exactly the two inheritance cases of `GreendlingerThreeFactor`'s
descent: the block buried in the second conjugator (`i = 0`) and the block
meeting the second rotation in a piece `v` (`i = |v|`).  So the hypothesis below
is a weakening of what that descent already proves, and the whole of the new
content is the case where the block runs further. -/
theorem landsIn_of_confined [DecidableEq α] {R : Set (List (α × Bool))}
    {c' t' : List (α × Bool)} {f : List (FreeGroup α × List (α × Bool))}
    {b i m : ℕ}
    (ht' : t' ∈ symmetrization R)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)))
    (hi : 6 * i < t'.length) (hfit : b ≤ c'.length + i)
    (hm : f.length < m) :
    LandsIn R b (conjEval ((FreeGroup.mk c', t') :: f)).toWord m := by
  refine ⟨c', t', f, [], 0, i, hm, ?_, ht', hredp', hmin, hi, by omega, ?_⟩
  · rw [List.drop_zero, List.nil_append]
  · rw [List.length_nil]
    omega

/-! ## The one hypothesis -/

/-- **Where the leading block stops.**  At the head of a minimal expression
whose leading cancellation reaches past its own trailing conjugator, either the
block leaves enough of the leading rotation standing for the located conclusion
to come from the leading factor itself, or it stops in a later factor, within a
sixth of that factor's rotation past its conjugator.

Compare `GreendlingerThreeFactor.LeadingConfinement`, which asks the block to
stop inside the palindrome of the factor *immediately* next --- a statement its
own header refutes --- and `TailSubwordBeyondBlock`, which asks for a located
subword of the tail and so cannot be checked factor by factor.  This asks only
where the block stops, and it asks it of the whole cascade rather than of one
neighbour, which is exactly the difference between the two. -/
def CascadeLanding [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → 6 * j < t.length →
    GreendlingerAt R (c.length + j) (P' ++ B') ∨
      (M.length + j ≤ c.length + t.length ∧
        LandsIn R M.length (conjEval e).toWord e.length)

/-! ## The descent, jumping along the cascade -/

/-- **The descent.**  For a minimal expression of any length whose leading
factor is in palindromic normal form, the reduced word contains more than half
of a symmetrized relator, beginning at or after position `|c| + j` for every
offset `j` below a sixth of the leading rotation.

The induction is on the number of factors, but a step is no longer one factor:
the block is handed to whichever factor it stops in, and the cascade carries the
subword that factor produces back across everything in between.  That is what
removes the adjacency assumption the four-case descent of
`GreendlingerThreeFactor` could not do without. -/
theorem greendlingerAt_of_cascadeLanding [DecidableEq α]
    {R : Set (List (α × Bool))} (hland : CascadeLanding R) :
    ∀ (n : ℕ) (e : List (FreeGroup α × List (α × Bool)))
      (c t w : List (α × Bool)) (j : ℕ),
      e.length ≤ n →
      FreeGroup.IsReduced w → t ∈ symmetrization R →
      FreeGroup.IsReduced (palindrome c t) →
      IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) (FreeGroup.mk w) →
      6 * j < t.length →
      GreendlingerAt R (c.length + j) w := by
  intro n
  induction n with
  | zero =>
      intro e c t w j hlen hw ht hredp hmin hj
      cases e with
      | cons x e' =>
          simp only [List.length_cons] at hlen
          exact absurd hlen (by omega)
      | nil =>
          obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
            exists_leading_cancellation hw hredp hmin.2.1
          have hnil : FreeGroup.invRev M ++ B' = [] := by
            rw [← hgw, conjEval_nil]
            exact FreeGroup.toWord_eq_nil_iff.mpr rfl
          have hz := congrArg List.length hnil
          rw [List.length_append, FreeGroup.invRev_length,
            List.length_nil] at hz
          rw [hwe]
          exact greendlingerAt_of_short_cancellation ht heq (by omega) hj
  | succ n ih =>
      intro e c t w j hlen hw ht hredp hmin hj
      obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
        exists_leading_cancellation hw hredp hmin.2.1
      have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
      rw [hwe]
      rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
      · exact greendlingerAt_of_short_cancellation ht heq hshort hj
      · rcases hland c t e (FreeGroup.mk w) P' M B' j hmin ht hredp heq hgw
            (by omega) hj with hdone | ⟨hhigh, hlands⟩
        · exact hdone
        · obtain ⟨c', t', f, A, N, i, hf, hV, ht', hredp', hminf, hi, hN, hMb⟩ :=
            hlands
          have hIH := ih f c' t'
            (conjEval ((FreeGroup.mk c', t') :: f)).toWord i
            (by omega) FreeGroup.isReduced_toWord ht' hredp'
            (by rw [FreeGroup.mk_toWord]; exact hminf) hi
          have htrans := hIH.transport A hN
          rw [← hV] at htrans
          exact greendlingerAt_inherit heq hgw hhigh (by omega) htrans

/-! ## The gate -/

/-- **The Greendlinger conclusion from a minimal expression of any length.** -/
theorem greendlinger_of_cascadeLanding [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hland : CascadeLanding R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {e : List (FreeGroup α × List (α × Bool))}
    (hmin : IsMinimalConjExpr R e (FreeGroup.mk w)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  cases e with
  | nil =>
      exfalso
      have hb := hmin.2.1
      rw [conjEval_nil] at hb
      have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
        rw [← FreeGroup.one_eq_mk]
        exact hb.symm
      have h2 := FreeGroup.reduce.sound h1
      rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
      exact hwne h2
  | cons x e'' =>
      obtain ⟨x₁, s₁⟩ := x
      obtain ⟨c, t, ht, hredp, hmin'⟩ := exists_palindromic_head hR hRne hmin
      have htpos : 0 < t.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
      exact greendlinger_of_greendlingerAt
        (greendlingerAt_of_cascadeLanding hland e''.length e'' c t w 0 le_rfl hw
          ht hredp hmin' (by omega))

/-- **The gate, for a `C'(1/6)` family whose leading blocks land.**  Every
nonempty reduced word in the normal closure contains more than half of a
symmetrized relator.

This supersedes `greendlingerConclusion_of_leadingConfinement`, whose hypothesis
is refuted by the configuration in `GreendlingerThreeFactor`'s header, and
`greendlinger_of_tailSubwordBeyondBlock`, whose hypothesis asks for a located
subword of the tail rather than for a position. -/
theorem greendlingerConclusion_of_cascadeLanding [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hland : CascadeLanding R) :
    GreendlingerConclusion R := by
  intro w hw hwne hmem
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R (FreeGroup.mk w)).mp hmem
  obtain ⟨e₀, hv₀, -, he₀⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩
  exact greendlinger_of_cascadeLanding hR hRne hland hw hwne hmin

end SmallCancellationRouter
end GroupApproximation
