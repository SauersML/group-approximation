import GroupApproximation.Sofic.BlockInfix

/-!
# Locating a block, and what a long boundary run buys

Two ends of the machine meet here.

**The output.**  `greendlinger_of_infix_of_infix` says what the count has to
deliver and no more: one word `F` that is a contiguous subword of `w` *and* a
contiguous subword of some symmetrized relator `t`, with `|t| < 2|F|`.  That is
already the Greendlinger conclusion --- rotate `t` so that `F` starts it, which
`symmetrization` allows.  So the whole remaining problem is to produce such an
`F`, and nothing about diagrams or curvature appears in this statement.

**The blocks.**  `labelledExpr_relator_eq` locates the `i`-th relator inside the
labelled word: everything before it and everything after it carries other labels.
With `BlockInfix` that turns "this run never leaves the label `relator i`" into
"the run's letters are a subword of the `i`-th relator", and the same for the
boundary block, where `invRev` has to be undone --- the boundary block spells
`w⁻¹`, so a run there gives a subword of `w` read backwards.

Unconditional.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The output: a long common subword is the conclusion -/

/-- **What the count has to deliver.**  A word that occurs both inside `w` and
inside a symmetrized relator, longer than half of that relator, *is* the
Greendlinger conclusion: rotating the relator to start at the occurrence keeps it
symmetrized and makes the occurrence a prefix. -/
theorem greendlinger_of_infix_of_infix {R : Set (List (α × Bool))}
    {w t F : List (α × Bool)} (ht : t ∈ symmetrization R) (hFw : F <:+: w)
    (hFt : F <:+: t) (hlong : t.length < 2 * F.length) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  obtain ⟨P, S, hPS⟩ := hFt
  refine ⟨t.rotate P.length, rotate_mem_symmetrization ht _, F, hFw, ?_, ?_⟩
  · exact prefix_rotate_of_append_prefix ⟨S, hPS⟩
  · rw [List.length_rotate]
    exact hlong

/-! ## Undoing the boundary block's inversion -/

/-- Formal inversion carries occurrences to occurrences. -/
theorem invRev_infix {L M : List (α × Bool)} (h : L <:+: M) :
    FreeGroup.invRev L <:+: FreeGroup.invRev M := by
  obtain ⟨P, S, hPS⟩ := h
  refine ⟨FreeGroup.invRev S, FreeGroup.invRev P, ?_⟩
  rw [← hPS, FreeGroup.invRev_append, FreeGroup.invRev_append, List.append_assoc]

/-- And back, since it is an involution. -/
theorem infix_of_invRev_infix {L M : List (α × Bool)}
    (h : FreeGroup.invRev L <:+: FreeGroup.invRev M) : L <:+: M := by
  have hb := invRev_infix h
  rwa [FreeGroup.invRev_invRev, FreeGroup.invRev_invRev] at hb

/-! ## Locating the `i`-th relator -/

/-- **The `i`-th relator sits in one piece**, with its own label, and nothing
else in the expression carries that label: what precedes it is the factors before
it together with its own conjugator, and what follows is its inverted conjugator
together with the factors after it. -/
theorem labelledExpr_relator_eq [DecidableEq α] :
    ∀ (k : ℕ) (e₁ : List (FreeGroup α × List (α × Bool))) (x : FreeGroup α)
      (s : List (α × Bool)) (e₂ : List (FreeGroup α × List (α × Bool))),
      labelledExpr k (e₁ ++ (x, s) :: e₂)
        = (labelledExpr k e₁ ++ tag (Block.conj (k + e₁.length)) x.toWord)
            ++ (tag (Block.relator (k + e₁.length)) s
              ++ (tag (Block.stem (k + e₁.length)) (FreeGroup.invRev x.toWord)
                ++ labelledExpr (k + e₁.length + 1) e₂)) := by
  intro k e₁
  induction e₁ generalizing k with
  | nil =>
      intro x s e₂
      rw [List.nil_append, labelledExpr_cons, labelledFactor]
      simp only [List.length_nil, Nat.add_zero, labelledExpr_nil, List.nil_append,
        List.append_assoc]
  | cons f e₁' ih =>
      intro x s e₂
      obtain ⟨y, r⟩ := f
      rw [List.cons_append, labelledExpr_cons, ih (k + 1) x s e₂]
      have hlen : k + 1 + e₁'.length = k + ((y, r) :: e₁').length := by
        simp only [List.length_cons]
        omega
      simp only [List.length_cons] at hlen
      simp only [List.length_cons, labelledExpr_cons, List.append_assoc]
      congr 2
      rw [hlen]

/-- Everything before the `i`-th relator block carries a different label. -/
theorem ne_relator_of_mem_before [DecidableEq α]
    (k : ℕ) (e₁ : List (FreeGroup α × List (α × Bool))) (x : FreeGroup α)
    (p : (α × Bool) × Block)
    (hp : p ∈ labelledExpr k e₁ ++ tag (Block.conj (k + e₁.length)) x.toWord) :
    p.2 ≠ Block.relator (k + e₁.length) := by
  rcases List.mem_append.mp hp with hp' | hp'
  · obtain ⟨j, -, hjlt, hlab⟩ := index_mem_range_of_mem_labelledExpr k e₁ p hp'
    rcases hlab with h | h | h
    · rw [h]
      exact Block.noConfusion
    · rw [h]
      intro hcon
      exact (Nat.ne_of_lt hjlt) (Block.relator.inj hcon)
    · rw [h]
      exact Block.noConfusion
  · rw [forall_mem_tag _ _ p hp']
    intro hcon
    exact Block.noConfusion hcon

end SmallCancellationRouter
end GroupApproximation
