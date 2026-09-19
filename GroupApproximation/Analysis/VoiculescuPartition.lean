import GroupApproximation.Analysis.VoiculescuMonotoneUnit

/-!
# (V4, general) The partition of unity the reduction runs on

The block-diagonal case of the assembly is closed
(`Analysis/VoiculescuBlockAbsorption`), and a general representation is *not*
block-diagonal — asking for one would be asking for quasidiagonality, which is
false.  Voiculescu's argument does not reduce `ρ` to a block-diagonal
representation at all.  It cuts the *space* instead, with a partition of unity
built from the quasicentral approximate unit:

    `dⱼ = (e_{j+1} - e_j)^{1/2}` ,   `Σⱼ dⱼ² = 1` ,

each `dⱼ` a positive compact contraction that asymptotically commutes with
`ρ(A)`.  This module states that datum and proves the one consequence the
assembly actually consumes.

## Why the squares, and not the `dⱼ` themselves

Because the isometry is assembled as `W = Σⱼ Vⱼ dⱼ` with the `Vⱼ` of pairwise
orthogonal ranges, and then

    `W⋆W = Σ_{j,k} dⱼ Vⱼ⋆ V_k d_k = Σⱼ dⱼ² = 1` ,

the cross terms dying on the orthogonality.  So what makes `W` an isometry is
exactly that the *squares* resolve the identity, and `tendsto_sum_norm_sq` below
is that fact in the form the assembly meets it: for every vector,
`Σⱼ ‖dⱼx‖² = ‖x‖²`.  That is this module's model test, and it is a consumer-form
test rather than a restatement — a datum whose squares summed to anything else,
or whose `dⱼ` were not self-adjoint, would fail it.

## What is owed

Three things, all named rather than assumed.  `(e_{j+1} - e_j)` is a positive
compact contraction — that is `MonotoneCompactUnit.succ_sub`, already proved, and
is why (V1c) records the order clauses.  Its square root is again compact,
because the compacts are a closed two-sided `⋆`-ideal and the non-unital
continuous calculus does not leave one
(`CStarIdealApproximateUnit.idealStarSub` puts them in that shape).  And the
square root still asymptotically commutes — which is *not* a quantitative
estimate: `Analysis/ShulmanCoronaSquareRootCommutator` does it qualitatively, by
turning a null commutator into an exact one in the corona and using that
functional calculus preserves exact commutation.

That qualitative clause is consistent and useful, but it is weaker than the
general V4 assembly needs.  The defect estimate in
`Analysis/VoiculescuSuperposition` sums the commutator norms, and convergence of
the individual norms to zero does not imply summability.  A later construction
must therefore select the monotone unit diagonally so that the square-root
commutators are summable for each member of the dense target family; the present
structure deliberately does not claim that stronger datum has been built.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology
open scoped InnerProductSpace

noncomputable section

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- **The partition of unity.**  Positive compacts whose squares resolve the
identity strongly and whose commutators with each member of a given countable
family are summable. -/
structure QuasicentralPartition (K : Type) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (S : ℕ → (K →L[ℂ] K)) where
  /-- The pieces. -/
  d : ℕ → (K →L[ℂ] K)
  /-- Each piece is positive. -/
  nonneg : ∀ j, 0 ≤ d j
  /-- Each piece is compact. -/
  isCompact : ∀ j, IsCompactOperator (d j)
  /-- The squares resolve the identity strongly. -/
  tendsto_sum_sq : ∀ x : K,
    Tendsto (fun N ↦ ∑ j ∈ Finset.range N, (d j * d j) x) atTop (𝓝 x)
  /-- The commutators are summable for each member of the target family.  This
  is the quantitative diagonal selection the superposition estimate consumes;
  mere convergence of the terms to zero is insufficient. -/
  summable_comm : ∀ k, Summable fun j ↦ ‖d j * S k - S k * d j‖

namespace QuasicentralPartition

variable {S : ℕ → (K →L[ℂ] K)} (P : QuasicentralPartition K S)

/-- Each piece is self-adjoint, being positive. -/
theorem isSelfAdjoint (j : ℕ) : IsSelfAdjoint (P.d j) :=
  IsSelfAdjoint.of_nonneg (P.nonneg j)

/-- The quadratic form of a square is a squared norm. -/
theorem inner_sq (j : ℕ) (x : K) :
    ⟪x, (P.d j * P.d j) x⟫_ℂ = ((‖P.d j x‖ : ℝ) : ℂ) ^ 2 := by
  have hadj : ContinuousLinearMap.adjoint (P.d j) = P.d j :=
    (ContinuousLinearMap.star_eq_adjoint (P.d j)).symm.trans (P.isSelfAdjoint j).star_eq
  have h : ⟪x, (P.d j * P.d j) x⟫_ℂ = ⟪P.d j x, P.d j x⟫_ℂ := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    nth_rewrite 1 [← hadj]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _
  rw [h, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **The model test, in the form the assembly consumes.**  The squares
resolving the identity is exactly `Σⱼ ‖dⱼx‖² = ‖x‖²`, which is what makes
`W = Σⱼ Vⱼ dⱼ` an isometry once the `Vⱼ` have orthogonal ranges.  A datum whose
squares summed to anything else, or whose pieces were not self-adjoint, fails
here. -/
theorem tendsto_sum_norm_sq (x : K) :
    Tendsto (fun N ↦ ∑ j ∈ Finset.range N, ‖P.d j x‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
  have hinner : Tendsto (fun N ↦ ⟪x, ∑ j ∈ Finset.range N, (P.d j * P.d j) x⟫_ℂ)
      atTop (𝓝 ⟪x, x⟫_ℂ) :=
    ((innerSL ℂ x).continuous.tendsto x).comp (P.tendsto_sum_sq x)
  have hfun : ∀ N, (⟪x, ∑ j ∈ Finset.range N, (P.d j * P.d j) x⟫_ℂ).re
      = ∑ j ∈ Finset.range N, ‖P.d j x‖ ^ 2 := by
    intro N
    rw [inner_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [P.inner_sq j x]
    norm_cast
  have hlim : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hre := (Complex.continuous_re.tendsto _).comp hinner
  rw [hlim] at hre
  exact hre.congr hfun

end QuasicentralPartition

/-- **The clause set is consistent.**  On a finite-dimensional space the single
piece `d₀ = 1`, with every later piece zero, satisfies every clause at once: the
squares reach the identity after one term, and a constant and a zero both commute
exactly.  So the datum is inhabited and no clause contradicts another — the check
a datum most needs before anything is built on it. -/
theorem exists_quasicentralPartition_of_finiteDimensional
    [FiniteDimensional ℂ K] (S : ℕ → (K →L[ℂ] K)) :
    Nonempty (QuasicentralPartition K S) := by
  haveI : ProperSpace K := FiniteDimensional.proper ℂ K
  have hone : IsCompactOperator ((1 : K →L[ℂ] K) : K → K) :=
    isCompactOperator_id_iff_locallyCompactSpace.mpr inferInstance
  refine ⟨{ d := fun j ↦ if j = 0 then 1 else 0
            nonneg := fun j ↦ by
              by_cases h : j = 0
              · rw [if_pos h]; exact zero_le_one
              · rw [if_neg h]
            isCompact := fun j ↦ by
              by_cases h : j = 0
              · rw [if_pos h]; exact hone
              · rw [if_neg h]; exact isCompactOperator_zero
            tendsto_sum_sq := fun x ↦ ?_
            summable_comm := fun k ↦ ?_ }⟩
  · refine tendsto_atTop_of_eventually_const (i₀ := 1) fun N hN ↦ ?_
    rw [Finset.sum_eq_single 0]
    · rw [if_pos rfl]
      rfl
    · intro j _ hj
      rw [if_neg hj]
      simp
    · intro h
      exact absurd (Finset.mem_range.mpr hN) h
  · have hzero : (fun j ↦ ‖(if j = 0 then 1 else 0) * S k -
        S k * (if j = 0 then 1 else 0)‖) = fun _ : ℕ ↦ (0 : ℝ) := by
      funext j
      by_cases h : j = 0
      · rw [if_pos h, one_mul, mul_one, sub_self, norm_zero]
      · rw [if_neg h, zero_mul, mul_zero, sub_self, norm_zero]
    rw [hzero]
    exact summable_zero

end

end ShulmanFill
end GroupApproximation
