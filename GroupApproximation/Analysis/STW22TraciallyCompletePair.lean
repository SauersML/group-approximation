import GroupApproximation.Analysis.STW22FactorialCore

/-!
# The uniform tracial completion is a tracially complete pair

`Analysis/STW22FactorialCore` proves that the designated traces of the bounded
uniform-two completion form a closed face of `T(M)`.  This file supplies the
other half of CCEGSTW Definition 3.4, so that the pair is a genuine
**factorial tracially complete C-star algebra**:

* `uniformTwoNormOn_designatedTraces`: `‖·‖_{2,X}` computed over the designated
  traces is exactly the completion gauge.  This is CCEGSTW Proposition 3.23(i),
  and it is what makes the abstract axioms say something about this concrete
  completion rather than about an unrelated supremum;
* `isFaithfulTraceSet_designatedTraces`: `X` is a faithful set of traces;
* `unitBallUniformTwoComplete_designatedTraces`: the unit ball of the completion
  is `‖·‖_{2,X}`-complete.

Faithfulness needs no extra hypothesis: the coordinate norm comparison
`‖z‖ ≤ r n · q n z`, which is already part of the completion data (it is what
makes the Cauchy quotient converge coordinatewise in operator norm), forces a
gauge-null element to vanish at every coordinate.

Completeness of the unit ball is not free either, but it is already available:
`exists_boundedCStarSequence_uniformTwoLimit` produces the limit inside the
bounded product and `mem_scalarPlusJ_of_uniformTwoLimit` puts it back in
`ℂ1 + J`, so the only work is transport through `realize` and the operator-norm
bound on the limit.
-/

namespace GroupApproximation
namespace STW22FactorialCore

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialCompletionIdentification
open UniformTracialBoundedCauchyQuotient
open UniformTracialGNSTwoGauge STW22Assembly
open STW22ActualTraceSpaces STW22BaseUniformTracialGauge
open STW22CanonicalTraceExtension
open TraciallyComplete

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))]

/-! ## The trace two-norm is subadditive in the reverse direction -/

theorem tracialTwoNorm_sub_le' {A : Type*} [CStarAlgebra A] (σ : TracialState A)
    (u v : A) :
    tracialTwoNorm σ u - tracialTwoNorm σ v ≤ tracialTwoNorm σ (u - v) := by
  have h := tracialTwoNorm_add_le σ (u - v) v
  rw [sub_add_cancel] at h
  linarith

/-! ## `‖·‖_{2,X}` is the completion gauge -/

/-- A canonical extension restricted to a base element has the base trace
two-norm. -/
theorem tracialTwoNorm_canonicalExtension_baseToCompletion {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (tau : TracialState (BaseAlgebra D)) (b : BaseAlgebra D) :
    tracialTwoNorm (canonicalExtension hr tau) (baseToCompletion (G D) hr b)
      = tracialTwoNorm tau b := by
  have h : Star.star (baseToCompletion (G D) hr b) * baseToCompletion (G D) hr b
      = baseToCompletion (G D) hr (Star.star b * b) := by
    rw [map_mul, map_star]
  rw [tracialTwoNorm_def, tracialTwoNorm_def, h,
    canonicalExtension_baseToCompletion_apply]

theorem uniformTwoNormOn_designatedTraces_le {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (x : BoundedUniformTwoCompletion (G D) r hr) :
    uniformTwoNormOn (designatedTraces hr) x ≤ completionGauge hr x :=
  uniformTwoNormOn_le (designatedTraces_nonempty hr) (fun σ hσ ↦ hσ x)

theorem completionGauge_le_uniformTwoNormOn {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (x : BoundedUniformTwoCompletion (G D) r hr) :
    completionGauge hr x ≤ uniformTwoNormOn (designatedTraces hr) x := by
  refine _root_.le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  -- a base approximant close enough in the gauge
  obtain ⟨b, hclose⟩ : ∃ b : BaseAlgebra D,
      uniformTwoNorm (G D)
        ((realize (G D) hr x - baseToScalarPlusJ (G D) b : M D) :
          BoundedCStarSequence D) < ε / 3 := by
    obtain ⟨k, hk⟩ := (Metric.tendsto_nhds.mp
      (chosenApproximation (realize (G D) hr x)).tendsto_two (ε / 3) hε3).exists
    refine ⟨(chosenApproximation (realize (G D) hr x)).seq k, ?_⟩
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (uniformTwoNorm_nonneg (G D) _)] at hk
    exact hk
  -- the gauge of `x` is within ε/3 of the gauge of the approximant
  have hcoe : ((realize (G D) hr x - baseToScalarPlusJ (G D) b : M D) :
      BoundedCStarSequence D) = (realize (G D) hr x).1 - b.1 := by
    rw [coe_sub_M]
    rfl
  rw [hcoe] at hclose
  have hgauge : completionGauge hr x ≤ uniformTwoNorm (G D) b.1 + ε / 3 := by
    have h1 := uniformTwoNorm_le_sub_add (realize (G D) hr x).1 b.1
    have hg : completionGauge hr x
        = uniformTwoNorm (G D) (realize (G D) hr x).1 := rfl
    rw [hg]
    linarith
  -- a base trace nearly attaining the base sup
  have hsup : uniformTwoNorm (G D) b.1 = baseTracialTwoSize b :=
    (baseTracialTwoSize_eq_uniformTwoNorm_allTraces b).symm
  have hlt : baseTracialTwoSize b - ε / 3
      < sSup (Set.range fun τ : TracialState (BaseAlgebra D) ↦
          tracialTwoNorm τ b) := by
    have hdef : baseTracialTwoSize b
        = sSup (Set.range fun τ : TracialState (BaseAlgebra D) ↦
            tracialTwoNorm τ b) := rfl
    rw [← hdef]
    linarith
  obtain ⟨v, hv, hvlt⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hlt
  obtain ⟨tau, rfl⟩ := hv
  -- the canonical extension of `tau` nearly attains the gauge at `x`
  have hmem : canonicalExtension hr tau ∈ designatedTraces hr :=
    fun z ↦ tracialTwoNorm_canonicalExtension_le hr tau z
  have hsplit : tracialTwoNorm (canonicalExtension hr tau)
        (baseToCompletion (G D) hr b)
      - tracialTwoNorm (canonicalExtension hr tau) x
      ≤ tracialTwoNorm (canonicalExtension hr tau)
          (baseToCompletion (G D) hr b - x) :=
    tracialTwoNorm_sub_le' _ _ _
  have hdist : tracialTwoNorm (canonicalExtension hr tau)
      (baseToCompletion (G D) hr b - x) < ε / 3 := by
    refine lt_of_le_of_lt (tracialTwoNorm_canonicalExtension_le hr tau _) ?_
    have hneg : completionGauge hr (baseToCompletion (G D) hr b - x)
        = completionGauge hr (x - baseToCompletion (G D) hr b) := by
      show uniformTwoNorm (G D)
          ((realize (G D) hr (baseToCompletion (G D) hr b - x)).1)
        = uniformTwoNorm (G D)
          ((realize (G D) hr (x - baseToCompletion (G D) hr b)).1)
      rw [realize_sub, realize_sub]
      exact uniformTwoNorm_sub_comm _ _
    rw [hneg, completionGauge_sub_baseToCompletion, hcoe]
    exact hclose
  have hbase : tracialTwoNorm (canonicalExtension hr tau)
      (baseToCompletion (G D) hr b) = tracialTwoNorm tau b :=
    tracialTwoNorm_canonicalExtension_baseToCompletion hr tau b
  have hx : tracialTwoNorm (canonicalExtension hr tau) x
      ≤ uniformTwoNormOn (designatedTraces hr) x :=
    tracialTwoNorm_le_uniformTwoNormOn hmem x
  rw [hbase] at hsplit
  rw [hsup] at hgauge
  linarith

theorem uniformTwoNormOn_designatedTraces {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (x : BoundedUniformTwoCompletion (G D) r hr) :
    uniformTwoNormOn (designatedTraces hr) x = completionGauge hr x :=
  le_antisymm (uniformTwoNormOn_designatedTraces_le hr x)
    (completionGauge_le_uniformTwoNormOn hr x)

/-- The abstract `‖·‖_{2,X}`-continuity of a trace and this project's concrete
`IsCompletionUniformTwoContinuous` are the same condition, because the two
gauges agree. -/
theorem isUniformTwoContinuousOn_iff_isCompletionUniformTwoContinuous
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (σ : TracialState (BoundedUniformTwoCompletion (G D) r hr)) :
    IsUniformTwoContinuousOn (designatedTraces hr) σ
      ↔ IsCompletionUniformTwoContinuous (G D) hr σ := by
  have hfun : ∀ x : ℕ → BoundedUniformTwoCompletion (G D) r hr,
      (fun k ↦ uniformTwoNormOn (designatedTraces hr) (x k))
        = fun k ↦ uniformTwoNorm (G D) ((realize (G D) hr (x k)).1) := by
    intro x
    funext k
    exact uniformTwoNormOn_designatedTraces hr (x k)
  constructor
  · intro h x hx
    refine h x ?_
    rw [hfun x]
    exact hx
  · intro h x hx
    refine h x ?_
    rw [hfun x] at hx
    exact hx

/-- **The designated traces are exactly the `‖·‖_{2,X}`-continuous traces**, in
the abstract vocabulary.  This is CCEGSTW Proposition 3.15 for this pair, and
it is what makes the two forms of Question 1.1 equivalent here. -/
theorem mem_designatedTraces_iff_isUniformTwoContinuousOn {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (σ : TracialState (BoundedUniformTwoCompletion (G D) r hr)) :
    σ ∈ designatedTraces hr ↔ IsUniformTwoContinuousOn (designatedTraces hr) σ :=
  (mem_designatedTraces_iff_isCompletionUniformTwoContinuous hr σ).trans
    (isUniformTwoContinuousOn_iff_isCompletionUniformTwoContinuous hr σ).symm

/-! ## Faithfulness -/

/-- **The completion gauge is a norm.**  No extra hypothesis is needed: the
coordinate norm comparison `‖z‖ ≤ r n · q n z`, which is already part of the
completion data, forces a gauge-null element to vanish coordinatewise. -/
theorem eq_zero_of_completionGauge_eq_zero
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    {x : BoundedUniformTwoCompletion (G D) r hr}
    (h : completionGauge hr x = 0) : x = 0 := by
  have hcoord : ∀ n : ℕ, (realize (G D) hr x).1 n = 0 := by
    intro n
    have h2 : (G D).q n ((realize (G D) hr x).1 n) ≤ completionGauge hr x :=
      q_le_uniformTwoNorm (G D) ((realize (G D) hr x).1) n
    rw [h] at h2
    have h3 : (G D).q n ((realize (G D) hr x).1 n) = 0 :=
      le_antisymm h2 ((G D).nonneg n _)
    have h4 := hr n ((realize (G D) hr x).1 n)
    rw [h3, mul_zero] at h4
    exact norm_le_zero_iff.1 h4
  have hz : (realize (G D) hr x).1 = 0 := by
    apply Subtype.ext
    funext n
    simpa using hcoord n
  have hz' : realize (G D) hr x = 0 := Subtype.ext hz
  have hzero : realize (G D) hr (0 : BoundedUniformTwoCompletion (G D) r hr) = 0 :=
    map_zero (realizationStarAlgEquiv (G D) hr)
  exact realize_injective (G D) hr (by rw [hz', hzero])

theorem isFaithfulTraceSet_designatedTraces
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r) :
    IsFaithfulTraceSet (designatedTraces hr) := by
  intro a ha
  refine eq_zero_of_completionGauge_eq_zero hr ?_
  rw [← uniformTwoNormOn_designatedTraces hr]
  refine le_antisymm ?_ (uniformTwoNormOn_nonneg (designatedTraces_nonempty hr) a)
  refine uniformTwoNormOn_le (designatedTraces_nonempty hr) fun σ hσ ↦ ?_
  rw [tracialTwoNorm_def, ha σ hσ]
  simp

/-! ## Completeness of the unit ball -/

theorem unitBallUniformTwoComplete_designatedTraces {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r) :
    UnitBallUniformTwoComplete (designatedTraces hr) := by
  intro x hx hcauchy
  have hnormeq : ∀ z : BoundedUniformTwoCompletion (G D) r hr,
      ‖(realize (G D) hr z).1‖ = ‖z‖ := fun _ ↦ rfl
  have hgaugeSub : ∀ z w : BoundedUniformTwoCompletion (G D) r hr,
      completionGauge hr (z - w)
        = uniformTwoNorm (G D) ((realize (G D) hr z).1 - (realize (G D) hr w).1) := by
    intro z w
    show uniformTwoNorm (G D) ((realize (G D) hr (z - w)).1) = _
    rw [realize_sub]
    rfl
  have hu_norm : ∀ k, ‖(realize (G D) hr (x k)).1‖ ≤ 1 := by
    intro k
    rw [hnormeq]
    exact hx k
  have hu_mem : ∀ k, (realize (G D) hr (x k)).1 ∈ scalarPlusJ (G D) := by
    intro k
    exact mem_scalarPlusJSubalgebra.1 (realize (G D) hr (x k)).2
  have hu_cauchy : ∀ ε > 0, ∃ K : ℕ, ∀ k, K ≤ k → ∀ l, K ≤ l → ∀ n,
      (G D).q n ((realize (G D) hr (x k)).1 n - (realize (G D) hr (x l)).1 n)
        < ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := hcauchy ε hε
    refine ⟨K, fun k hk l hl n ↦ ?_⟩
    have hlt := hK k hk l hl
    rw [uniformTwoNormOn_designatedTraces hr, hgaugeSub] at hlt
    refine lt_of_le_of_lt ?_ hlt
    exact q_le_uniformTwoNorm (G D) _ n
  obtain ⟨y, hycoord, hyconv⟩ :=
    exists_boundedCStarSequence_uniformTwoLimit (G D) hr
      (fun k ↦ (realize (G D) hr (x k)).1) hu_norm hu_cauchy
  have hy_mem : y ∈ scalarPlusJ (G D) :=
    mem_scalarPlusJ_of_uniformTwoLimit (G D) hu_mem hyconv
  have hy_norm : ‖y‖ ≤ 1 := by
    refine lp.norm_le_of_forall_le zero_le_one fun n ↦ ?_
    have hnorm : Tendsto (fun k ↦ ‖(realize (G D) hr (x k)).1 n‖) atTop
        (nhds ‖y n‖) := (continuous_norm.tendsto (y n)).comp (hycoord n)
    refine le_of_tendsto hnorm (Eventually.of_forall fun k ↦ ?_)
    exact (boundedCStarSequence_coord_norm_le D _ n).trans (hu_norm k)
  obtain ⟨a, ha⟩ := realize_surjective (G D) hr ⟨y, mem_scalarPlusJSubalgebra.2 hy_mem⟩
  refine ⟨a, ?_, ?_⟩
  · rw [← hnormeq a, ha]
    exact hy_norm
  · refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    obtain ⟨K, hK⟩ := hyconv (ε / 2) (by linarith)
    filter_upwards [eventually_ge_atTop K] with k hk
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (uniformTwoNormOn_nonneg (designatedTraces_nonempty hr) _)]
    rw [uniformTwoNormOn_designatedTraces hr, hgaugeSub, ha]
    refine lt_of_le_of_lt (uniformTwoNorm_le (G D) _ (c := ε / 2) fun n ↦ ?_)
      (by linarith)
    show (G D).q n ((realize (G D) hr (x k)).1 n - y n) ≤ ε / 2
    rw [(G D).sub_comm_eq n _ _]
    exact (hK k hk n).le

/-! ## The pair -/

/-- **The uniform tracial completion is a tracially complete C-star algebra**
in the sense of CCEGSTW Definition 3.4. -/
theorem isTraciallyCompletePair_designatedTraces {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r) :
    IsTraciallyCompletePair (designatedTraces hr) where
  nonempty := designatedTraces_nonempty hr
  isCompact := isCompact_designatedTraces hr
  isConvex := isConvexTraceSet_designatedTraces hr
  faithful := isFaithfulTraceSet_designatedTraces hr
  unitBallComplete := unitBallUniformTwoComplete_designatedTraces hr

/-- **The uniform tracial completion is a factorial tracially complete C-star
algebra**, CCEGSTW Definitions 3.4 and 3.13.  This is the hypothesis of STW
Problem XXII. -/
theorem isFactorialTraciallyCompletePair_designatedTraces {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r) :
    IsFactorialTraciallyCompletePair (designatedTraces hr) where
  toIsTraciallyCompletePair := isTraciallyCompletePair_designatedTraces hr
  isClosed := isClosed_designatedTraces hr
  isFace := isFaceTraceSet_designatedTraces hr

/-- **The two forms of the trace problem agree for this pair.**  CCEGSTW
Question 1.1 asks either "are all traces `‖·‖_{2,X}`-continuous?" or,
equivalently, "is `X ⊆ T(M)` an equality?"; for a factorial pair those coincide,
and here that coincidence is a theorem. -/
theorem allTracesUniformTwoContinuous_iff_designatedTracesAreAllTraces'
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r) :
    AllTracesUniformTwoContinuous (designatedTraces hr)
      ↔ DesignatedTracesAreAllTraces (designatedTraces hr) :=
  allTracesUniformTwoContinuous_iff_designatedTracesAreAllTraces
    (mem_designatedTraces_iff_isUniformTwoContinuousOn hr)

end

end STW22FactorialCore
end GroupApproximation
