import GroupApproximation.Analysis.TraciallyCompleteCStar

/-!
# Model tests for the tracially complete and factorial pair Props

Repository standing order: every hypothesis-bearing `Prop` is instantiated at
the smallest object in reach, and refuted where that is cheap, so a vacuous
definition cannot pass.  `Analysis/TraciallyCompleteCStar` introduces
`IsFaithfulTraceSet`, `IsUniformTwoContinuousOn`, `UnitBallUniformTwoComplete`,
`IsConvexTraceSet`, `IsFaceTraceSet`, `IsTraciallyCompletePair`,
`IsFactorialTraciallyCompletePair` (CCEGSTW, arXiv:2310.20594, Definitions 3.4
and 3.13), `AllTracesUniformTwoContinuous` and `DesignatedTracesAreAllTraces`
(the two forms of CCEGSTW Question 1.1).  This file tests all of them.

* **Positive model: `(ℂ, T(ℂ))`.**  `ℂ` has one tracial state, its uniform
  two-norm is the modulus, and the pair is factorial tracially complete.  The
  trace problem has the positive answer there, in both forms.
* **Negative models on `ℂ × ℂ`.**  `fstTrace` and `sndTrace` are the two
  coordinate traces and `midTrace` is their midpoint.
  - `{fstTrace}` is a closed face, but it is not faithful, so the pair is not
    tracially complete; `sndTrace` is not `‖·‖_{2,X}`-continuous for it, so both
    forms of the trace problem fail there.
  - `{midTrace}` is not a face, so it is not factorial.
  - `{fstTrace, sndTrace}` is not convex.
* `UnitBallUniformTwoComplete` has no cheap negative model: on a
  finite-dimensional algebra every faithful uniform two-norm is equivalent to the
  operator norm, so a failure needs an infinite-dimensional algebra.
-/

namespace GroupApproximation
namespace TraciallyCompleteModelTest

open Filter
open TraciallyComplete
open UniformTracialGNSTwoGauge
open scoped ComplexOrder

noncomputable section

/-! ## The positive model `(ℂ, T(ℂ))` -/

theorem uniformTwoNormOn_univ_complex (a : ℂ) :
    uniformTwoNormOn (Set.univ : Set (TracialState ℂ)) a = ‖a‖ := by
  refine le_antisymm
    (uniformTwoNormOn_le ⟨UniformTracialGNSTwoGauge.complexTracialState, Set.mem_univ _⟩ ?_) ?_
  · intro τ _
    exact (tracialTwoNorm_complex τ a).le
  · exact (tracialTwoNorm_complex UniformTracialGNSTwoGauge.complexTracialState a).symm.le.trans
      (tracialTwoNorm_le_uniformTwoNormOn (Set.mem_univ _) a)

theorem isConvexTraceSet_univ_complex :
    IsConvexTraceSet (Set.univ : Set (TracialState ℂ)) :=
  fun _ _ _ _ _ _ _ ↦ Set.mem_univ _

theorem isFaceTraceSet_univ_complex :
    IsFaceTraceSet (Set.univ : Set (TracialState ℂ)) :=
  ⟨isConvexTraceSet_univ_complex, fun _ _ _ _ _ _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩⟩

theorem isFaithfulTraceSet_univ_complex :
    IsFaithfulTraceSet (Set.univ : Set (TracialState ℂ)) := by
  intro a h
  have h1 := h UniformTracialGNSTwoGauge.complexTracialState (Set.mem_univ _)
  rw [tracialState_complex_eq] at h1
  exact (CStarRing.star_mul_self_eq_zero_iff a).mp h1

theorem unitBallUniformTwoComplete_univ_complex :
    UnitBallUniformTwoComplete (Set.univ : Set (TracialState ℂ)) := by
  intro x hx hcauchy
  have hc : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := hcauchy ε hε
    refine ⟨K, fun k hk l hl ↦ ?_⟩
    have h := hK k hk l hl
    rwa [uniformTwoNormOn_univ_complex, ← dist_eq_norm] at h
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨a, le_of_tendsto' ha.norm hx, ?_⟩
  have hd := (tendsto_iff_dist_tendsto_zero.mp ha)
  simpa only [uniformTwoNormOn_univ_complex, dist_eq_norm] using hd

/-- **Positive model.**  `(ℂ, T(ℂ))` is a factorial tracially complete pair. -/
theorem isFactorialTraciallyCompletePair_univ_complex :
    IsFactorialTraciallyCompletePair (Set.univ : Set (TracialState ℂ)) := by
  haveI := compactSpace_tracialState ℂ
  exact ⟨⟨⟨UniformTracialGNSTwoGauge.complexTracialState, Set.mem_univ _⟩, isCompact_univ,
    isConvexTraceSet_univ_complex, isFaithfulTraceSet_univ_complex,
    unitBallUniformTwoComplete_univ_complex⟩, isClosed_univ, isFaceTraceSet_univ_complex⟩

/-- The trace problem has the positive answer at `(ℂ, T(ℂ))`, first form. -/
theorem allTracesUniformTwoContinuous_univ_complex :
    AllTracesUniformTwoContinuous (Set.univ : Set (TracialState ℂ)) := fun σ ↦
  isUniformTwoContinuousOn_of_norm_le (C := 1) fun a ↦
    le_of_eq (by rw [one_mul, uniformTwoNormOn_univ_complex, tracialState_complex_eq])

/-- The trace problem has the positive answer at `(ℂ, T(ℂ))`, second form. -/
theorem designatedTracesAreAllTraces_univ_complex :
    DesignatedTracesAreAllTraces (Set.univ : Set (TracialState ℂ)) :=
  rfl

/-! ## Negative models on `ℂ × ℂ` -/

/-- Evaluation at the first coordinate. -/
def fstTrace : TracialState (ℂ × ℂ) where
  toLinearMap := LinearMap.fst ℂ ℂ ℂ
  map_one := rfl
  map_star_mul_self_nonneg x := by
    change (0 : ℂ) ≤ star x.1 * x.1
    exact star_mul_self_nonneg x.1
  map_mul_comm x y := by
    change x.1 * y.1 = y.1 * x.1
    exact mul_comm x.1 y.1

/-- Evaluation at the second coordinate. -/
def sndTrace : TracialState (ℂ × ℂ) where
  toLinearMap := LinearMap.snd ℂ ℂ ℂ
  map_one := rfl
  map_star_mul_self_nonneg x := by
    change (0 : ℂ) ≤ star x.2 * x.2
    exact star_mul_self_nonneg x.2
  map_mul_comm x y := by
    change x.2 * y.2 = y.2 * x.2
    exact mul_comm x.2 y.2

@[simp] theorem fstTrace_apply (a : ℂ × ℂ) : fstTrace a = a.1 := rfl

@[simp] theorem sndTrace_apply (a : ℂ × ℂ) : sndTrace a = a.2 := rfl

/-- The midpoint of the two coordinate traces. -/
def midTrace : TracialState (ℂ × ℂ) :=
  convexComb (1 / 2) (by norm_num) (by norm_num) fstTrace sndTrace

/-- The second minimal projection `(0, 1)`. -/
def secondUnit : ℂ × ℂ := (0, 1)

theorem star_mul_self_secondUnit : star secondUnit * secondUnit = secondUnit := by
  ext <;> simp [secondUnit]

theorem apply_secondUnit_eq_zero {σ : TracialState (ℂ × ℂ)}
    (h : (σ secondUnit).re = 0) : σ secondUnit = 0 := by
  have hnn := σ.map_star_mul_self_nonneg secondUnit
  rw [star_mul_self_secondUnit] at hnn
  obtain ⟨-, him⟩ := Complex.nonneg_iff.mp hnn
  exact Complex.ext (by rw [h, Complex.zero_re]) (by rw [← him, Complex.zero_im])

theorem re_apply_secondUnit_nonneg (σ : TracialState (ℂ × ℂ)) :
    0 ≤ (σ secondUnit).re := by
  have hnn := σ.map_star_mul_self_nonneg secondUnit
  rw [star_mul_self_secondUnit] at hnn
  exact (Complex.nonneg_iff.mp hnn).1

theorem eq_fstTrace_of_apply_secondUnit {σ : TracialState (ℂ × ℂ)}
    (h : σ secondUnit = 0) : σ = fstTrace := by
  apply tracialState_ext
  intro a
  have ha : a = a.1 • (1 : ℂ × ℂ) + (a.2 - a.1) • secondUnit := by
    ext <;> simp [secondUnit]
  conv_lhs => rw [ha]
  rw [TracialState.map_add, TracialState.map_smul, TracialState.map_smul,
    TracialState.apply_one, h, fstTrace_apply]
  simp

/-- `{fstTrace}` is a face of `T(ℂ × ℂ)`. -/
theorem isFaceTraceSet_singleton_fstTrace :
    IsFaceTraceSet ({fstTrace} : Set (TracialState (ℂ × ℂ))) := by
  refine ⟨?_, ?_⟩
  · intro σ hσ τ hτ t ht0 ht1
    rw [Set.mem_singleton_iff] at hσ hτ ⊢
    subst hσ
    subst hτ
    apply tracialState_ext
    intro a
    simp only [convexComb_apply, fstTrace_apply]
    push_cast
    ring
  · intro σ τ t ht0 ht1 h
    rw [Set.mem_singleton_iff] at h
    have hval : (convexComb t ht0.le ht1.le σ τ secondUnit).re = 0 := by
      rw [h, fstTrace_apply]
      simp [secondUnit]
    rw [convexComb_re] at hval
    have hσ := re_apply_secondUnit_nonneg σ
    have hτ := re_apply_secondUnit_nonneg τ
    have h1t : 0 < 1 - t := by linarith
    have hσt := mul_nonneg ht0.le hσ
    have hτt := mul_nonneg h1t.le hτ
    have htx : t * (σ secondUnit).re = 0 := by linarith
    have hty : (1 - t) * (τ secondUnit).re = 0 := by linarith
    exact ⟨Set.mem_singleton_iff.mpr (eq_fstTrace_of_apply_secondUnit
        (apply_secondUnit_eq_zero ((mul_eq_zero.mp htx).resolve_left ht0.ne'))),
      Set.mem_singleton_iff.mpr (eq_fstTrace_of_apply_secondUnit
        (apply_secondUnit_eq_zero ((mul_eq_zero.mp hty).resolve_left h1t.ne')))⟩

/-- `fstTrace` is `‖·‖_{2,{fstTrace}}`-continuous. -/
theorem isUniformTwoContinuousOn_fstTrace :
    IsUniformTwoContinuousOn ({fstTrace} : Set (TracialState (ℂ × ℂ))) fstTrace :=
  isUniformTwoContinuousOn_of_norm_le (C := 1) fun a ↦ by
    rw [one_mul]
    exact (norm_apply_le_tracialTwoNorm fstTrace a).trans
      (tracialTwoNorm_le_uniformTwoNormOn (Set.mem_singleton _) a)

/-- **Negative model.**  `{fstTrace}` does not see `(0, 1)`, so it is not faithful. -/
theorem not_isFaithfulTraceSet_singleton_fstTrace :
    ¬ IsFaithfulTraceSet ({fstTrace} : Set (TracialState (ℂ × ℂ))) := by
  intro hf
  have h0 : secondUnit = 0 := hf secondUnit fun τ hτ ↦ by
    rw [Set.mem_singleton_iff] at hτ
    subst hτ
    rw [star_mul_self_secondUnit, fstTrace_apply]
    simp [secondUnit]
  simpa [secondUnit] using congrArg Prod.snd h0

theorem not_isTraciallyCompletePair_singleton_fstTrace :
    ¬ IsTraciallyCompletePair ({fstTrace} : Set (TracialState (ℂ × ℂ))) :=
  fun h ↦ not_isFaithfulTraceSet_singleton_fstTrace h.faithful

theorem not_isTraciallyCompletePair_empty :
    ¬ IsTraciallyCompletePair (∅ : Set (TracialState ℂ)) :=
  fun h ↦ Set.not_nonempty_empty h.nonempty

/-- **Negative model.**  `{midTrace}` is not a face. -/
theorem not_isFaceTraceSet_singleton_midTrace :
    ¬ IsFaceTraceSet ({midTrace} : Set (TracialState (ℂ × ℂ))) := by
  intro hface
  have hmem := (hface.mem_of_convexComb_mem fstTrace sndTrace (1 / 2) (by norm_num)
    (by norm_num) (Set.mem_singleton_iff.mpr rfl)).1
  rw [Set.mem_singleton_iff] at hmem
  have h := congrArg (fun σ : TracialState (ℂ × ℂ) ↦ (σ ((1, 0) : ℂ × ℂ)).re) hmem
  simp only [midTrace, convexComb_re, fstTrace_apply, sndTrace_apply] at h
  norm_num at h

theorem not_isFactorialTraciallyCompletePair_singleton_midTrace :
    ¬ IsFactorialTraciallyCompletePair ({midTrace} : Set (TracialState (ℂ × ℂ))) :=
  fun h ↦ not_isFaceTraceSet_singleton_midTrace h.isFace

/-- **Negative model.**  `{fstTrace, sndTrace}` is not convex. -/
theorem not_isConvexTraceSet_pair :
    ¬ IsConvexTraceSet ({fstTrace, sndTrace} : Set (TracialState (ℂ × ℂ))) := by
  intro hconv
  have hmem := hconv fstTrace (by simp) sndTrace (by simp) (1 / 2) (by norm_num) (by norm_num)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · have h2 := congrArg (fun σ : TracialState (ℂ × ℂ) ↦ (σ secondUnit).re) h
    simp only [convexComb_re, fstTrace_apply, sndTrace_apply, secondUnit] at h2
    norm_num at h2
  · have h2 := congrArg (fun σ : TracialState (ℂ × ℂ) ↦ (σ secondUnit).re) h
    simp only [convexComb_re, fstTrace_apply, sndTrace_apply, secondUnit] at h2
    norm_num at h2

/-- **Negative model.**  `sndTrace` is not `‖·‖_{2,{fstTrace}}`-continuous. -/
theorem not_isUniformTwoContinuousOn_sndTrace :
    ¬ IsUniformTwoContinuousOn ({fstTrace} : Set (TracialState (ℂ × ℂ))) sndTrace := by
  intro hc
  have hnorm : uniformTwoNormOn ({fstTrace} : Set (TracialState (ℂ × ℂ))) secondUnit = 0 := by
    refine le_antisymm (uniformTwoNormOn_le (Set.singleton_nonempty _) ?_)
      (uniformTwoNormOn_nonneg (Set.singleton_nonempty _) _)
    intro τ hτ
    rw [Set.mem_singleton_iff] at hτ
    subst hτ
    rw [tracialTwoNorm_def, star_mul_self_secondUnit, fstTrace_apply]
    simp [secondUnit]
  have hx : Tendsto (fun _ : ℕ ↦
      uniformTwoNormOn ({fstTrace} : Set (TracialState (ℂ × ℂ))) secondUnit) atTop (nhds 0) := by
    rw [hnorm]
    exact tendsto_const_nhds
  have h := hc (fun _ ↦ secondUnit) hx
  have h' : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 0) := by
    simpa only [sndTrace_apply, secondUnit] using h
  exact zero_ne_one (tendsto_nhds_unique h' tendsto_const_nhds)

/-- The trace problem fails for `{fstTrace}`, first form. -/
theorem not_allTracesUniformTwoContinuous_singleton_fstTrace :
    ¬ AllTracesUniformTwoContinuous ({fstTrace} : Set (TracialState (ℂ × ℂ))) :=
  fun h ↦ not_isUniformTwoContinuousOn_sndTrace (h sndTrace)

/-- The trace problem fails for `{fstTrace}`, second form. -/
theorem not_designatedTracesAreAllTraces_singleton_fstTrace :
    ¬ DesignatedTracesAreAllTraces ({fstTrace} : Set (TracialState (ℂ × ℂ))) := by
  intro h
  have hmem : sndTrace ∈ ({fstTrace} : Set (TracialState (ℂ × ℂ))) :=
    Set.eq_univ_iff_forall.mp h sndTrace
  rw [Set.mem_singleton_iff] at hmem
  have h2 := congrArg (fun σ : TracialState (ℂ × ℂ) ↦ σ secondUnit) hmem
  simp only [fstTrace_apply, sndTrace_apply, secondUnit] at h2
  exact one_ne_zero h2

end

end TraciallyCompleteModelTest
end GroupApproximation
