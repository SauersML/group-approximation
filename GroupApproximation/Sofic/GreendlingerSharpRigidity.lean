import GroupApproximation.Sofic.GreendlingerDeepOverrunCount

/-!
# The sharp rigidity core

Every deep-regime argument in this lane bottoms out in one statement: a word
prefixing two symmetrized relators and long enough relative to the first is not
a piece, so the two relators coincide.  `GreendlingerDeepArc` states it at the
constant `1/6` (`eq_of_sixth_common_prefix`), where "long enough" is
`|s| ≤ 6|p|` and the contradiction closes by `omega`.

That constant is the only reason the deep side is pinned to `λ = 1/6`.  The
hypothesis it consumes, `MetricSmallCancellation R lam`, is *already* stated
rationally --- every piece satisfies `|p| < λ|w|` --- so the `1/6` in
`eq_of_sixth_common_prefix` is not coming from the small-cancellation
condition.  It is an artifact of clearing the denominator once, in
`GreendlingerPiece.six_mul_length_lt_of_isPiece`, so that everything downstream
could be discharged in `ℕ`.

This file removes that artifact.  `eq_of_lam_common_prefix` is the same three
lines with `linarith` in place of `omega`, and it holds at every `λ`, not only
at a sixth.  The two consumers the deep regime actually uses are twinned on top
of it.

## What this is worth

Nothing here is new mathematics: the classical `C'(λ)` rigidity statement is
exactly this, and the `λ`-free file is its `λ = 1/6` evaluation.  What it buys
is that the deep side's base no longer forces the whole tower down to a single
constant, which is what
`GreendlingerSharpResidualWiring.SharpResiduals` needs and what the router's
consumers cannot supply, since `torsionFree_of_residuals` asks for `λ ≤ 1/8`.

The intrusion bound additionally needs `λ ≤ 1`, which is free in range, because
the alignment may run past the whole of the landing rotation and the `take`
then saturates; at `λ = 1/6` that case was invisible inside `omega`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The rigidity core at an arbitrary constant -/

/-- **A `λ`-fraction is already rigid.**  The `λ`-twin of
`GreendlingerDeepArc.eq_of_sixth_common_prefix`.

A word prefixing two symmetrized relators and occupying at least a `λ`-fraction
of the first is not a piece, because `C'(λ)` bounds every piece strictly below
that fraction; so the two relators are equal.  The `λ`-free version is this
statement at `λ = 1/6` with the denominator cleared. -/
theorem eq_of_lam_common_prefix {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {p s s' : List (α × Bool)}
    (hs : s ∈ symmetrization R) (hs' : s' ∈ symmetrization R)
    (hps : p <+: s) (hps' : p <+: s')
    (hlong : lam * (s.length : ℚ) ≤ (p.length : ℚ)) : s = s' := by
  by_contra hne
  have hpiece : IsPiece (symmetrization R) p :=
    isPiece_of_prefix_two hs hs' hne hps hps'
  have h := hmetric p hpiece s hs hps
  linarith

/-! ## 2.  The intrusion lands in the head relator -/

/-- **The `λ`-twin of `GreendlingerDeepArc.eq_rotate_of_deep_intrusion`.**

An eaten stretch occupying at least a `λ`-fraction of the rotation it came out
of, prefixing a rotation of a symmetrized relator, forces that rotation to be
the inverted head rotation.  Proof and shape are quoted from the `λ`-free
version; only the fraction moves. -/
theorem eq_rotate_of_deep_intrusion_sharp {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {t t' E : List (α × Bool)} {k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t) (hlong : lam * (t.length : ℚ) ≤ (E.length : ℚ))
    (hintr : FreeGroup.invRev E <+: t'.rotate k) :
    FreeGroup.invRev t = t'.rotate k := by
  refine eq_of_lam_common_prefix hmetric (invRev_mem_symmetrization ht)
    (rotate_mem_symmetrization ht' k) (invRev_prefix_of_suffix hEt) hintr ?_
  rw [FreeGroup.invRev_length, FreeGroup.invRev_length]
  exact hlong

/-! ## 3.  The front piece bound at an arbitrary constant -/

/-- **The intrusion into the landing rotation is a piece, at any `λ`.**  The
`λ`-twin of `GreendlingerDeepOverrunCount.six_mul_intrusion_lt_of_forward`.

The alignment makes `t₃.take i` a common prefix of `t₃` and of a rotation of
`invRev t`; if it reached `λ|t₃|` the two would coincide, and the coincidence
is refuted by `ne_rotate_invRev_of_minimal_forward`.

`λ ≤ 1` is read only in the saturating branch, where the alignment ran past the
whole of `t₃` and `take` returns `t₃` itself.  At `λ = 1/6` that branch was
absorbed by `omega`; stated rationally it has to be split. -/
theorem intrusion_lt_of_forward_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam1 : lam ≤ 1)
    (hmetric : MetricSmallCancellation R lam)
    {c t c₃ t₃ dw y : List (α × Bool)} {i : ℕ}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))) g)
    (ht : t ∈ symmetrization R) (ht₃ : t₃ ∈ symmetrization R)
    (hd : FreeGroup.mk dw = conjEval e₁ * FreeGroup.mk c₃)
    (hcy : dw = c ++ y) (hy : y <+: FreeGroup.invRev t)
    (halign : t₃.take i <+: (FreeGroup.invRev t).rotate y.length) :
    (i : ℚ) < lam * (t₃.length : ℚ) := by
  by_contra hcon
  have hcon' : lam * (t₃.length : ℚ) ≤ (i : ℚ) := not_lt.mp hcon
  refine ne_rotate_invRev_of_minimal_forward hmin hd hcy hy ?_
  refine eq_of_lam_common_prefix hmetric ht₃
    (rotate_mem_symmetrization (invRev_mem_symmetrization ht) y.length)
    (List.take_prefix i t₃) halign ?_
  rw [List.length_take]
  rcases le_total i t₃.length with hle | hle
  · rw [min_eq_left hle]
    exact hcon'
  · rw [min_eq_right hle]
    nlinarith [(Nat.cast_nonneg t₃.length : (0 : ℚ) ≤ (t₃.length : ℚ))]

end SmallCancellationRouter
end GroupApproximation
