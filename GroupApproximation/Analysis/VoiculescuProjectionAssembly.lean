import GroupApproximation.Analysis.VoiculescuProjectionSequence

/-!
# (V1a), closed

`SeparableProjectionSequenceStatement` is the last input (V1a) owed, and
`Analysis/VoiculescuProjectionSequence` built the two pieces Mathlib lacks.
This module assembles them: the projections onto the prefix spans of a dense
sequence are compact self-adjoint contractions converging strongly to the
identity, so `exists_sequentialCompactUnit` applies and every separable Hilbert
space has a sequential approximate unit for its compacts.

The convergence is where the assembly does real work.  `‖v - P n v‖` is
antitone, because the spans increase and `norm_sub_starProjection_le` says the
projection beats every other member of its subspace; it is bounded below by
zero; so `tendsto_atTop_ciInf` gives convergence to the infimum, and the
infimum is zero because the sequence is dense and `d k` already lies in the
`(k+1)`-st span.  Antitonicity is what makes this a limit rather than a liminf,
and it is the only reason the prefix spans are taken increasing.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

section Assembly

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- **The prefix projections converge strongly to the identity.** -/
theorem tendsto_starProjection_densePrefixSpan (d : ℕ → H) (hd : DenseRange d)
    (v : H) :
    Tendsto (fun n ↦ (densePrefixSpan d n).starProjection v) atTop (𝓝 v) := by
  set f : ℕ → ℝ := fun n ↦ ‖v - (densePrefixSpan d n).starProjection v‖ with hf
  have hanti : Antitone f := by
    intro m n hmn
    refine norm_sub_starProjection_le _ v ?_
    exact densePrefixSpan_mono d hmn
      ((densePrefixSpan d m).starProjection_apply_mem v)
  have hbdd : BddBelow (Set.range f) := ⟨0, by
    rintro _ ⟨n, rfl⟩
    exact norm_nonneg _⟩
  have hinf : (⨅ n, f n) = 0 := by
    refine le_antisymm ?_ (le_ciInf fun n ↦ norm_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hd v ε hε
    refine le_trans (ciInf_le hbdd (k + 1)) ?_
    have hle : f (k + 1) ≤ ‖v - d k‖ :=
      norm_sub_starProjection_le _ v (mem_densePrefixSpan d k)
    rw [dist_comm, dist_eq_norm] at hk
    rw [norm_sub_rev] at hk
    linarith
  have hlim : Tendsto f atTop (𝓝 0) := by
    rw [← hinf]
    exact tendsto_atTop_ciInf hanti hbdd
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine hlim.congr fun n ↦ ?_
  rw [hf, norm_sub_rev]

/-- **(V1a)'s last input, discharged.** -/
theorem separableProjectionSequence : SeparableProjectionSequenceStatement := by
  intro H _ _ _ _
  haveI : Nonempty H := ⟨0⟩
  refine ⟨fun n ↦ (densePrefixSpan (TopologicalSpace.denseSeq H) n).starProjection,
    fun n ↦ isCompactOperator_starProjection _, fun n ↦ ?_,
    fun n ↦ Submodule.starProjection_norm_le _, fun v ↦ ?_⟩
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (densePrefixSpan (TopologicalSpace.denseSeq H) n).starProjection_isSymmetric
  · exact tendsto_starProjection_densePrefixSpan _
      (TopologicalSpace.denseRange_denseSeq H) v

/-- **(V1a).**  Every separable Hilbert space has a sequential approximate unit
for its compacts, self-adjoint and contractive throughout. -/
theorem nonempty_sequentialCompactUnit (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] :
    Nonempty (SequentialCompactUnit H) :=
  exists_sequentialCompactUnit strongToNormOnCompacts separableProjectionSequence H

end Assembly

end

end ShulmanFill
end GroupApproximation
