import GroupApproximation.Analysis.VoiculescuIsometryRepair
import GroupApproximation.Analysis.VoiculescuGlimmStatement

/-!
# (V3) The one-step approximation, and the seam it is cut at

`Analysis/VoiculescuPlan` describes **(V3)** in prose and names no `Prop` for it:
given a finite subset of a C⋆-subalgebra `A ⊆ B(H)` meeting the compacts only in
`0`, a tolerance, an obstruction subspace, and a representation of `A` on a
finite-dimensional space, produce an isometry `W` of that space into `H` avoiding
the obstruction with `W⋆ a W` within the tolerance of `ρ(a)`.  This module writes
the statement, writes the statement of the step Glimm's lemma actually delivers,
and proves that the two are equivalent.

## Where the cut is, and why there

Voiculescu's argument runs Glimm's lemma not on `A` but on the amplification
`Mₙ(A) ⊆ B(Hⁿ)`, at the state `[a_ij] ↦ (1/n) Σ ⟪ρ(a_ij) e_j, e_i⟫`, and reads
the resulting unit vector of `Hⁿ` as an `n`-tuple `(ξ₁, …, ξₙ)` of vectors of
`H`.  Taking `a = 1` in the finite set says the `√n ξ_k` are almost orthonormal;
taking `a` in the given finite set says the matrix `(⟪a ξ_l, ξ_k⟫)` almost
reproduces `ρ(a)`.  So what the amplification produces is not an isometry but a
**frame**: a map `T : K₀ → H` whose Gram operator `T⋆T` is merely *close* to `1`.

`FrameApproximationStatement` below is that output, and `oneStep_of_frame` is the
rest of Voiculescu's step: the frame is corrected to an isometry by
`Analysis/VoiculescuIsometryRepair`, whose correction is a right multiplier and so
preserves the escape from the obstruction subspace.  The cut is at the frame
because everything before it is the amplification — a construction — and
everything after it is an estimate that needs no hypothesis at all.

The cut costs nothing: `frameApproximation_of_oneStep` proves the converse, an
isometry being a frame with zero defect, so the two `Prop`s are equivalent and
the seam is not a strengthening of what Voiculescu proves.

## What the arithmetic of the correction is

At Gram defect `δ` the correction moves the compression by at most
`‖T⋆aT‖·2δ·(2δ+2)`, so with `M` a bound for `‖ρ(a)‖` on the finite set and
`δ ≤ 1/2` the total error is at most `6δ(M+1) + δ`.  Running the frame at
tolerance `min(1/2, ε/(12(M+1)))` leaves that below `ε`.  `M` is taken to be the
sum of the `‖ρ(a)‖` over the finite set rather than their maximum, which needs no
nonemptiness hypothesis and is what `Finset.single_le_sum` bounds.

## The hypotheses are not vacuous

They force `H` to be infinite-dimensional, by
`not_finiteDimensional_of_compactMem_eq_zero` — the same check that refuted
`Theorem4PrintedPairStatement`, and the reason both statements below carry `A`'s
intersection with the compacts rather than some weaker faithfulness.  The
representation space `K₀` is unconstrained: at `K₀ = 0` both statements hold with
`W = 0`, which is correct rather than degenerate, since a unital representation on
the zero space exists only when `A` itself is zero.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-! ## The two statements -/

/-- **(V3) Voiculescu's one-step approximation.**  A finite-dimensional
representation of `A` is approximated, on any finite set and to any tolerance, by
compression along an isometry whose range avoids a prescribed finite-dimensional
subspace. -/
def OneStepApproximationStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)), IsClosed (A : Set (H →L[ℂ] H)) →
      (∀ T ∈ A, IsCompactOperator T → T = 0) →
      ∀ (K₀ : Type) [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
        [FiniteDimensional ℂ K₀] [CompleteSpace K₀]
        (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) (F : Finset ↥A) (eps : ℝ), 0 < eps →
          ∀ V : Submodule ℂ H, FiniteDimensional ℂ V →
            ∃ W : K₀ →L[ℂ] H,
              ContinuousLinearMap.adjoint W ∘L W = 1 ∧
              (∀ x, W x ∈ Vᗮ) ∧
              ∀ a ∈ F, ‖ContinuousLinearMap.adjoint W ∘L (a : H →L[ℂ] H) ∘L W
                - rho a‖ < eps

/-- **(V3a) The frame the amplified Glimm lemma delivers.**  The same data, with
the isometry weakened to a map whose Gram operator is merely close to `1`.  This
is what Glimm's lemma on `Mₙ(A) ⊆ B(Hⁿ)` produces: the almost-orthonormality of
the `n`-tuple it returns is the case `a = 1` of its own conclusion, and is
approximate for the same reason every other entry is. -/
def FrameApproximationStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)), IsClosed (A : Set (H →L[ℂ] H)) →
      (∀ T ∈ A, IsCompactOperator T → T = 0) →
      ∀ (K₀ : Type) [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
        [FiniteDimensional ℂ K₀] [CompleteSpace K₀]
        (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) (F : Finset ↥A) (eps : ℝ), 0 < eps →
          ∀ V : Submodule ℂ H, FiniteDimensional ℂ V →
            ∃ T : K₀ →L[ℂ] H,
              (∀ x, T x ∈ Vᗮ) ∧
              ‖ContinuousLinearMap.adjoint T ∘L T - 1‖ < eps ∧
              ∀ a ∈ F, ‖ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T
                - rho a‖ < eps

/-! ## The seam is not a strengthening -/

/-- An isometry is a frame with zero Gram defect, so the one-step statement
implies the frame statement outright.  With `oneStep_of_frame` this makes the two
equivalent, which is the check that the cut above is where Voiculescu's argument
actually divides. -/
theorem frameApproximation_of_oneStep (h : OneStepApproximationStatement) :
    FrameApproximationStatement := by
  intro H _ _ _ A hAclosed hAK K₀ _ _ _ _ rho F eps heps V hV
  obtain ⟨W, hWiso, hWV, hWF⟩ := h H A hAclosed hAK K₀ rho F eps heps V hV
  refine ⟨W, hWV, ?_, hWF⟩
  rw [hWiso, sub_self, norm_zero]
  exact heps

/-! ## The frame, corrected -/

/-- **(V3) from the frame.**  The correction of `Analysis/VoiculescuIsometryRepair`
turns the frame into an isometry without moving its range, and the tolerance
`min(1/2, ε/(12(M+1)))` absorbs the correction's degradation. -/
theorem oneStep_of_frame (h : FrameApproximationStatement) :
    OneStepApproximationStatement := by
  intro H _ _ _ A hAclosed hAK K₀ _ _ _ _ rho F eps heps V hV
  set M : ℝ := ∑ a ∈ F, ‖rho a‖ with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun a _ ↦ norm_nonneg _
  have hMpos : (0:ℝ) < 12 * (M + 1) := by linarith
  set eta : ℝ := min (1/2) (eps / (12 * (M + 1))) with hetadef
  have heta0 : 0 < eta := lt_min (by norm_num) (div_pos heps hMpos)
  have hetahalf : eta ≤ 1/2 := min_le_left _ _
  have hetadiv : eta ≤ eps / (12 * (M + 1)) := min_le_right _ _
  have hkey : eta * (12 * (M + 1)) ≤ eps := (le_div_iff₀ hMpos).mp hetadiv
  have hkey12 : 12 * eta ≤ eps := by nlinarith [mul_nonneg heta0.le hM0]
  obtain ⟨T, hTV, hTgram, hTF⟩ := h H A hAclosed hAK K₀ rho F eta heta0 V hV
  have hgramhalf : ‖ContinuousLinearMap.adjoint T ∘L T - 1‖ ≤ 1/2 :=
    le_of_lt (lt_of_lt_of_le hTgram hetahalf)
  obtain ⟨c, hc, hcnorm, hciso, hcest⟩ := exists_isometry_of_norm_gram_le T hgramhalf
  have hk0 : (0:ℝ) ≤ ‖c - 1‖ := norm_nonneg _
  have hk2 : ‖c - 1‖ ≤ 2 * eta := hcnorm.trans (by linarith)
  have hk3 : ‖c - 1‖ + 2 ≤ 3 := by linarith
  refine ⟨T ∘L c, hciso, fun x ↦ comp_mem_of_mem T c _ hTV x, ?_⟩
  intro a ha
  have hMa : ‖rho a‖ ≤ M :=
    Finset.single_le_sum (f := fun b ↦ ‖rho b‖) (fun i _ ↦ norm_nonneg _) ha
  have hFa : ‖ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T - rho a‖ < eta :=
    hTF a ha
  have hTa : ‖ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T‖ ≤ M + 1 := by
    have hrw : ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T
        = (ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T - rho a) + rho a := by
      abel
    calc ‖ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T‖
        = ‖(ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T - rho a) + rho a‖ := by
          rw [← hrw]
      _ ≤ ‖ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T - rho a‖ + ‖rho a‖ :=
          norm_add_le _ _
      _ ≤ M + 1 := by linarith
  have hprod1 : ‖ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T‖ * ‖c - 1‖
      ≤ (M + 1) * (2 * eta) :=
    mul_le_mul hTa hk2 hk0 (by linarith)
  have hprod2 : ‖ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T‖ * ‖c - 1‖
        * (‖c - 1‖ + 2) ≤ (M + 1) * (2 * eta) * 3 :=
    mul_le_mul hprod1 hk3 (by linarith)
      (mul_nonneg (by linarith) (by linarith))
  have hring : (M + 1) * (2 * eta) * 3 = eta * (12 * (M + 1)) / 2 := by ring
  have hhalf : (M + 1) * (2 * eta) * 3 ≤ eps / 2 := by rw [hring]; linarith
  have hsplit : ContinuousLinearMap.adjoint (T ∘L c) ∘L (a : H →L[ℂ] H) ∘L (T ∘L c)
        - rho a
      = (ContinuousLinearMap.adjoint (T ∘L c) ∘L (a : H →L[ℂ] H) ∘L (T ∘L c)
          - ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T)
        + (ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T - rho a) := by
    abel
  calc ‖ContinuousLinearMap.adjoint (T ∘L c) ∘L (a : H →L[ℂ] H) ∘L (T ∘L c) - rho a‖
      = ‖(ContinuousLinearMap.adjoint (T ∘L c) ∘L (a : H →L[ℂ] H) ∘L (T ∘L c)
          - ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T)
        + (ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T - rho a)‖ := by
        rw [← hsplit]
    _ ≤ ‖ContinuousLinearMap.adjoint (T ∘L c) ∘L (a : H →L[ℂ] H) ∘L (T ∘L c)
          - ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T‖
        + ‖ContinuousLinearMap.adjoint T ∘L (a : H →L[ℂ] H) ∘L T - rho a‖ :=
        norm_add_le _ _
    _ < eps / 2 + eta :=
        add_lt_add_of_le_of_lt ((hcest (a : H →L[ℂ] H)).trans (hprod2.trans hhalf)) hFa
    _ ≤ eps := by linarith

/-! ## The model test -/

/-- **The hypotheses of both statements force an infinite-dimensional space.**  A
subalgebra meeting the compacts only in `0` contains `1`, and in finite dimensions
`1` is compact.  Recorded here as well as at `GlimmLemmaStatement` because the two
statements above carry the hypothesis independently, and a statement whose
hypotheses secretly pin `H` to a finite dimension is a statement about nothing. -/
theorem oneStep_not_finiteDimensional {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0) :
    ¬ FiniteDimensional ℂ H :=
  not_finiteDimensional_of_compactMem_eq_zero A hAK

end

end ShulmanFill
end GroupApproximation
