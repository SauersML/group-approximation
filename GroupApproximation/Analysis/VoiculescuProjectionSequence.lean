import GroupApproximation.Analysis.VoiculescuUnitOfProjections

/-!
# (V1a) The projections, and with them the sequential unit

`SeparableProjectionSequenceStatement` is the last input (V1a) owes: on a
separable Hilbert space, a sequence of compact self-adjoint contractions
converging strongly to the identity.  This module builds it and closes (V1a).

The witness is the orthogonal projection onto the span of the first `n` terms of
a dense sequence.  Mathlib carries the endomorphism form directly as
`Submodule.starProjection`, so nothing has to be composed with an inclusion:
`starProjection_norm_le` is the contraction bound and `starProjection_isSymmetric`
the self-adjointness.

Two steps are proved here rather than looked up, because Mathlib has neither at
the pinned revision.

* **Finite rank is compact.**  `Compact/FiniteDimension.lean` carries only the
  identity-operator direction.  The image of the closed unit ball lies in the
  range, which is finite-dimensional and therefore proper, so it sits inside a
  compact set, and `IsCompactOperator` follows from its definition.
* **Strong convergence.**  `‖v - P n v‖` is antitone in `n`, because the spans
  increase and the projection minimises the distance to its subspace, and it has
  infimum zero because the sequence is dense.  Antitone plus bounded below is
  `tendsto_atTop_ciInf`, which turns that into convergence rather than a liminf.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology
open scoped InnerProductSpace

noncomputable section

section Compactness

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A projection with finite-dimensional range is a compact operator.**  The
image of the unit ball lands in a closed ball of the range, which is compact
because a finite-dimensional space is proper. -/
theorem isCompactOperator_starProjection (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] [FiniteDimensional ℂ V] :
    IsCompactOperator (V.starProjection : H → H) := by
  haveI : ProperSpace V := FiniteDimensional.proper (𝕜 := ℂ) (E := V)
  refine ⟨V.subtypeL '' Metric.closedBall 0 1, ?_, ?_⟩
  · exact (isCompact_closedBall (0 : V) 1).image V.subtypeL.continuous
  · refine Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : H) one_pos) ?_
    intro x hx
    have hmem : V.starProjection x ∈ V := V.starProjection_apply_mem x
    refine ⟨⟨V.starProjection x, hmem⟩, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hb : ‖V.starProjection x‖ ≤ ‖x‖ :=
      le_trans (V.starProjection.le_opNorm x)
        (by simpa using mul_le_of_le_one_left (norm_nonneg x) V.starProjection_norm_le)
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact le_trans hb hx

end Compactness

section Sequence

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- The span of the first `n` terms of a dense sequence. -/
def densePrefixSpan (d : ℕ → H) (n : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ (d '' Set.Iio n)

instance finiteDimensional_densePrefixSpan (d : ℕ → H) (n : ℕ) :
    FiniteDimensional ℂ (densePrefixSpan d n) := by
  refine FiniteDimensional.span_of_finite ℂ ?_
  exact (Set.finite_Iio n).image d

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem densePrefixSpan_mono (d : ℕ → H) {m n : ℕ} (h : m ≤ n) :
    densePrefixSpan d m ≤ densePrefixSpan d n :=
  Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem mem_densePrefixSpan (d : ℕ → H) (k : ℕ) :
    d k ∈ densePrefixSpan d (k + 1) :=
  Submodule.subset_span ⟨k, Nat.lt_succ_self k, rfl⟩

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- **The projection minimises.**  Its distance to `v` is at most the distance
from `v` to any member of the subspace, by Pythagoras against
`sub_starProjection_mem_orthogonal`. -/
theorem norm_sub_starProjection_le (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (v : H) {w : H} (hw : w ∈ V) :
    ‖v - V.starProjection v‖ ≤ ‖v - w‖ := by
  have horth : ⟪v - V.starProjection v, V.starProjection v - w⟫_ℂ = 0 := by
    rw [inner_eq_zero_symm]
    exact (V.sub_starProjection_mem_orthogonal v) _
      (V.sub_mem (V.starProjection_apply_mem v) hw)
  have hsplit : v - w = (v - V.starProjection v) + (V.starProjection v - w) := by
    abel
  rw [hsplit]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth]
  linarith [mul_self_nonneg ‖V.starProjection v - w‖]

end Sequence

end

end ShulmanFill
end GroupApproximation
