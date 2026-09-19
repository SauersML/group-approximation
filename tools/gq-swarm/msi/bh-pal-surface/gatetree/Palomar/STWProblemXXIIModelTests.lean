/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Palomar.STWProblemXXIIChallenge

/-!
# Model tests for the Problem XXII challenge

Every `Prop` of `Palomar/STWProblemXXIIChallenge.lean` is exercised on a small instance, and refuted
where that is cheap.

* `TracialState` and its topology: the identity is the only tracial state on `ℂ`; the coordinate
  projections of `ℂ × ℂ` and their midpoint are tracial states; evaluation is continuous.
* **Positive model `(ℂ, T(ℂ))`.** `‖·‖_{2,T(ℂ)}` is the modulus. `T(ℂ)` is compact, convex, a face
  and faithful, and the unit ball is complete, so the pair is factorial tracially complete. Its trace
  is continuous, and the identity presents it as the tracial completion of `ℂ`.
* **Negative models.**
  - `∅` is neither faithful nor tracially complete, the trace of `ℂ` is not
    `‖·‖_{2,∅}`-continuous, and the identity with `∅` fails the restriction clause.
  - On `ℂ × ℂ`: `{fstTrace}` is not faithful, and `sndTrace` is not
    `‖·‖_{2,{fstTrace}}`-continuous; `{fstTrace, sndTrace}` is not convex; `{midTrace}` is not a
    face, so it is not factorial.
  - The diagonal `ℂ → ℂ × ℂ` fails the uniqueness clause for `T(ℂ × ℂ)` and the density clause for
    `{midTrace}`.
* `UnitBallUniformTwoComplete` has no small negative model: on a finite-dimensional algebra a
  faithful `‖·‖_{2,X}` is equivalent to the norm, so a failure needs an infinite-dimensional algebra.

The prose of this module was written by Claude (Anthropic).
-/

namespace STWProblemXXII
namespace ModelTests

open Filter
open scoped ComplexOrder

noncomputable section

/-! ### Tracial states -/

theorem tracialState_ext {A : Type*} [CStarAlgebra A] {σ τ : TracialState A}
    (h : ∀ a, σ.toLinearMap a = τ.toLinearMap a) : σ = τ := by
  cases σ with
  | mk f hf1 hfp hft =>
    cases τ with
    | mk g hg1 hgp hgt =>
      have hfg : f = g := LinearMap.ext h
      subst hfg
      rfl

theorem continuous_toLinearMap_apply {A : Type*} [CStarAlgebra A] (a : A) :
    Continuous fun τ : TracialState A ↦ τ.toLinearMap a := by
  have h : Continuous fun (τ : TracialState A) (b : A) ↦ τ.toLinearMap b := continuous_induced_dom
  exact (continuous_apply a).comp h

theorem complex_add_nonneg {z w : ℂ} (hz : 0 ≤ z) (hw : 0 ≤ w) : 0 ≤ z + w := by
  obtain ⟨hz1, hz2⟩ := Complex.nonneg_iff.mp hz
  obtain ⟨hw1, hw2⟩ := Complex.nonneg_iff.mp hw
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · rw [Complex.add_re]
    exact add_nonneg hz1 hw1
  · rw [Complex.add_im, ← hz2, ← hw2, add_zero]

theorem ofReal_mul_nonneg {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 0 ≤ z) : 0 ≤ (t : ℂ) * z := by
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hz
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg ht hre
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, ← him, mul_zero]

/-- The convex combination `tσ + (1 - t)τ` of two tracial states. -/
def convexComb {A : Type*} [CStarAlgebra A] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (σ τ : TracialState A) : TracialState A where
  toLinearMap := (t : ℂ) • σ.toLinearMap + ((1 - t : ℝ) : ℂ) • τ.toLinearMap
  map_one := by
    change (t : ℂ) * σ.toLinearMap 1 + ((1 - t : ℝ) : ℂ) * τ.toLinearMap 1 = 1
    rw [σ.map_one, τ.map_one, mul_one, mul_one, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  map_star_mul_self_nonneg x := by
    change 0 ≤ (t : ℂ) * σ.toLinearMap (star x * x) +
      ((1 - t : ℝ) : ℂ) * τ.toLinearMap (star x * x)
    exact complex_add_nonneg (ofReal_mul_nonneg ht0 (σ.map_star_mul_self_nonneg x))
      (ofReal_mul_nonneg (sub_nonneg.2 ht1) (τ.map_star_mul_self_nonneg x))
  map_mul_comm x y := by
    change (t : ℂ) * σ.toLinearMap (x * y) + ((1 - t : ℝ) : ℂ) * τ.toLinearMap (x * y) =
      (t : ℂ) * σ.toLinearMap (y * x) + ((1 - t : ℝ) : ℂ) * τ.toLinearMap (y * x)
    rw [σ.map_mul_comm, τ.map_mul_comm]

theorem convexComb_apply {A : Type*} [CStarAlgebra A] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (σ τ : TracialState A) (a : A) :
    (convexComb t ht0 ht1 σ τ).toLinearMap a =
      (t : ℂ) * σ.toLinearMap a + ((1 - t : ℝ) : ℂ) * τ.toLinearMap a :=
  rfl

theorem complex_star_mul_self_nonneg (z : ℂ) : (0 : ℂ) ≤ star z * z := by
  have h : ((Complex.normSq z : ℝ) : ℂ) = star z * z := Complex.normSq_eq_conj_mul_self
  rw [← h]
  exact Complex.zero_le_real.2 (Complex.normSq_nonneg z)

theorem re_star_mul_self (z : ℂ) : (star z * z).re = Complex.normSq z := by
  have h : ((Complex.normSq z : ℝ) : ℂ) = star z * z := Complex.normSq_eq_conj_mul_self
  rw [← h, Complex.ofReal_re]

/-- The identity is a tracial state on `ℂ`. -/
def complexTracialState : TracialState ℂ where
  toLinearMap := LinearMap.id
  map_one := rfl
  map_star_mul_self_nonneg z := complex_star_mul_self_nonneg z
  map_mul_comm z w := mul_comm z w

/-- The unit condition pins a tracial state on `ℂ`: it is the identity. -/
theorem tracialState_complex_apply (τ : TracialState ℂ) (z : ℂ) : τ.toLinearMap z = z := by
  have h := map_smul τ.toLinearMap z (1 : ℂ)
  simp only [smul_eq_mul, mul_one, τ.map_one] at h
  exact h

instance : Subsingleton (TracialState ℂ) :=
  ⟨fun σ τ ↦ tracialState_ext fun z ↦
    (tracialState_complex_apply σ z).trans (tracialState_complex_apply τ z).symm⟩

/-! ### The positive model `(ℂ, T(ℂ))` -/

theorem univ_nonempty_complex : (Set.univ : Set (TracialState ℂ)).Nonempty :=
  ⟨complexTracialState, Set.mem_univ _⟩

/-- On `ℂ`, `‖·‖_{2,X}` is the modulus for every non-empty `X`. -/
theorem uniformTwoNorm_complex {X : Set (TracialState ℂ)} (hX : X.Nonempty) (z : ℂ) :
    uniformTwoNorm X z = ‖z‖ := by
  obtain ⟨τ, hτ⟩ := hX
  rw [uniformTwoNorm, Set.subsingleton_of_subsingleton.eq_singleton_of_mem hτ, Set.image_singleton,
    csSup_singleton]
  show Real.sqrt (τ.toLinearMap (star z * z)).re = ‖z‖
  rw [tracialState_complex_apply, re_star_mul_self, Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg z)]

theorem isFaithfulTraceSet_univ : IsFaithfulTraceSet (Set.univ : Set (TracialState ℂ)) := by
  intro a h
  have h1 := h complexTracialState (Set.mem_univ _)
  rw [tracialState_complex_apply] at h1
  exact (CStarRing.star_mul_self_eq_zero_iff a).mp h1

theorem unitBallUniformTwoComplete_univ :
    UnitBallUniformTwoComplete (Set.univ : Set (TracialState ℂ)) := by
  intro x hx hcauchy
  have hc : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := hcauchy ε hε
    refine ⟨K, fun k hk l hl ↦ ?_⟩
    have h := hK k hk l hl
    rwa [uniformTwoNorm_complex univ_nonempty_complex, ← dist_eq_norm] at h
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨a, le_of_tendsto' ha.norm hx, ?_⟩
  have hd := tendsto_iff_dist_tendsto_zero.mp ha
  simpa only [uniformTwoNorm_complex univ_nonempty_complex, dist_eq_norm] using hd

theorem isConvexTraceSet_univ : IsConvexTraceSet (Set.univ : Set (TracialState ℂ)) :=
  fun _ _ _ _ _ _ _ _ _ ↦ Set.mem_univ _

theorem isFaceTraceSet_univ : IsFaceTraceSet (Set.univ : Set (TracialState ℂ)) :=
  ⟨isConvexTraceSet_univ, fun _ _ _ _ _ _ _ _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩⟩

theorem isTraciallyComplete_univ : IsTraciallyComplete (Set.univ : Set (TracialState ℂ)) where
  nonempty := univ_nonempty_complex
  isCompact := Set.subsingleton_of_subsingleton.isCompact
  isConvex := isConvexTraceSet_univ
  faithful := isFaithfulTraceSet_univ
  unitBallComplete := unitBallUniformTwoComplete_univ

theorem isFactorialTraciallyComplete_univ :
    IsFactorialTraciallyComplete (Set.univ : Set (TracialState ℂ)) :=
  ⟨isTraciallyComplete_univ, isClosed_univ, isFaceTraceSet_univ⟩

theorem isUniformTwoContinuous_univ (σ : TracialState ℂ) :
    IsUniformTwoContinuous (Set.univ : Set (TracialState ℂ)) σ := by
  intro x hx
  simp only [uniformTwoNorm_complex univ_nonempty_complex] at hx
  simp only [tracialState_complex_apply]
  exact tendsto_zero_iff_norm_tendsto_zero.2 hx

theorem isUniformTracialCompletion_id :
    IsUniformTracialCompletion (StarAlgHom.id ℂ ℂ) (Set.univ : Set (TracialState ℂ)) where
  isTraciallyComplete := isTraciallyComplete_univ
  existsUnique_restrict τ := ⟨complexTracialState, ⟨Set.mem_univ _, fun a ↦
      (tracialState_complex_apply _ _).trans (tracialState_complex_apply τ a).symm⟩,
    fun σ _ ↦ Subsingleton.elim σ _⟩
  dense m := by
    have h0 : uniformTwoNorm (Set.univ : Set (TracialState ℂ)) (m - StarAlgHom.id ℂ ℂ m) = 0 := by
      rw [uniformTwoNorm_complex univ_nonempty_complex]
      exact norm_eq_zero.2 (sub_self m)
    exact ⟨fun _ ↦ m, tendsto_const_nhds.congr fun _ ↦ h0.symm⟩

/-! ### Negative models on `ℂ` -/

theorem not_isFaithfulTraceSet_empty : ¬ IsFaithfulTraceSet (∅ : Set (TracialState ℂ)) :=
  fun h ↦ one_ne_zero (h 1 fun τ hτ ↦ (Set.not_nonempty_empty ⟨τ, hτ⟩).elim)

theorem not_isTraciallyComplete_empty : ¬ IsTraciallyComplete (∅ : Set (TracialState ℂ)) :=
  fun h ↦ Set.not_nonempty_empty h.nonempty

theorem not_isFactorialTraciallyComplete_empty :
    ¬ IsFactorialTraciallyComplete (∅ : Set (TracialState ℂ)) :=
  fun h ↦ not_isTraciallyComplete_empty h.isTraciallyComplete

theorem not_isUniformTwoContinuous_empty :
    ¬ IsUniformTwoContinuous (∅ : Set (TracialState ℂ)) complexTracialState := by
  intro hc
  have h0 : uniformTwoNorm (∅ : Set (TracialState ℂ)) (1 : ℂ) = 0 := by
    rw [uniformTwoNorm, Set.image_empty, Real.sSup_empty]
  have hx : Tendsto (fun _ : ℕ ↦ uniformTwoNorm (∅ : Set (TracialState ℂ)) (1 : ℂ)) atTop
      (nhds 0) := by
    rw [h0]
    exact tendsto_const_nhds
  have h' : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 0) := hc (fun _ ↦ 1) hx
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h')

theorem not_isUniformTracialCompletion_id_empty :
    ¬ IsUniformTracialCompletion (StarAlgHom.id ℂ ℂ) (∅ : Set (TracialState ℂ)) := by
  intro h
  obtain ⟨σ, ⟨hσ, -⟩, -⟩ := h.existsUnique_restrict complexTracialState
  exact Set.not_nonempty_empty ⟨σ, hσ⟩

/-! ### Negative models on `ℂ × ℂ` -/

/-- Evaluation at the first coordinate. -/
def fstTrace : TracialState (ℂ × ℂ) where
  toLinearMap := LinearMap.fst ℂ ℂ ℂ
  map_one := rfl
  map_star_mul_self_nonneg x := complex_star_mul_self_nonneg x.1
  map_mul_comm x y := mul_comm x.1 y.1

/-- Evaluation at the second coordinate. -/
def sndTrace : TracialState (ℂ × ℂ) where
  toLinearMap := LinearMap.snd ℂ ℂ ℂ
  map_one := rfl
  map_star_mul_self_nonneg x := complex_star_mul_self_nonneg x.2
  map_mul_comm x y := mul_comm x.2 y.2

theorem fstTrace_apply (a : ℂ × ℂ) : fstTrace.toLinearMap a = a.1 := rfl

theorem sndTrace_apply (a : ℂ × ℂ) : sndTrace.toLinearMap a = a.2 := rfl

/-- The midpoint of the two coordinate traces. -/
def midTrace : TracialState (ℂ × ℂ) :=
  convexComb (1 / 2) (by norm_num) (by norm_num) fstTrace sndTrace

theorem not_isFaithfulTraceSet_singleton_fstTrace :
    ¬ IsFaithfulTraceSet ({fstTrace} : Set (TracialState (ℂ × ℂ))) := by
  intro hf
  have h0 : ((0, 1) : ℂ × ℂ) = 0 := hf (0, 1) fun τ hτ ↦ by
    rw [Set.mem_singleton_iff] at hτ
    subst hτ
    show star (0 : ℂ) * 0 = 0
    rw [mul_zero]
  simpa using congrArg Prod.snd h0

theorem not_isUniformTwoContinuous_sndTrace :
    ¬ IsUniformTwoContinuous ({fstTrace} : Set (TracialState (ℂ × ℂ))) sndTrace := by
  intro hc
  have h0 : uniformTwoNorm ({fstTrace} : Set (TracialState (ℂ × ℂ))) ((0, 1) : ℂ × ℂ) = 0 := by
    rw [uniformTwoNorm, Set.image_singleton, csSup_singleton]
    show Real.sqrt (star (0 : ℂ) * 0).re = 0
    rw [mul_zero, Complex.zero_re, Real.sqrt_zero]
  have hx : Tendsto (fun _ : ℕ ↦
      uniformTwoNorm ({fstTrace} : Set (TracialState (ℂ × ℂ))) ((0, 1) : ℂ × ℂ)) atTop
      (nhds 0) := by
    rw [h0]
    exact tendsto_const_nhds
  have h' : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 0) := hc (fun _ ↦ (0, 1)) hx
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h')

theorem not_isConvexTraceSet_pair :
    ¬ IsConvexTraceSet ({fstTrace, sndTrace} : Set (TracialState (ℂ × ℂ))) := by
  intro hconv
  have hmem := hconv fstTrace (by simp) sndTrace (by simp) (1 / 2) (by norm_num) (by norm_num)
    midTrace fun _ ↦ rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · have h2 := congrArg (fun σ : TracialState (ℂ × ℂ) ↦ σ.toLinearMap ((0, 1) : ℂ × ℂ)) h
    simp only [midTrace, convexComb_apply, fstTrace_apply, sndTrace_apply] at h2
    norm_num at h2
  · have h2 := congrArg (fun σ : TracialState (ℂ × ℂ) ↦ σ.toLinearMap ((1, 0) : ℂ × ℂ)) h
    simp only [midTrace, convexComb_apply, fstTrace_apply, sndTrace_apply] at h2
    norm_num at h2

theorem not_isFaceTraceSet_singleton_midTrace :
    ¬ IsFaceTraceSet ({midTrace} : Set (TracialState (ℂ × ℂ))) := by
  intro hface
  have hmem := (hface.2 fstTrace sndTrace (1 / 2) (by norm_num) (by norm_num) midTrace
    (fun _ ↦ rfl) (Set.mem_singleton _)).1
  rw [Set.mem_singleton_iff] at hmem
  have h := congrArg (fun σ : TracialState (ℂ × ℂ) ↦ σ.toLinearMap ((1, 0) : ℂ × ℂ)) hmem
  simp only [midTrace, convexComb_apply, fstTrace_apply, sndTrace_apply] at h
  norm_num at h

theorem not_isFactorialTraciallyComplete_singleton_midTrace :
    ¬ IsFactorialTraciallyComplete ({midTrace} : Set (TracialState (ℂ × ℂ))) :=
  fun h ↦ not_isFaceTraceSet_singleton_midTrace h.isFace

/-- The diagonal embedding `z ↦ (z, z)`. -/
def diagonal : ℂ →⋆ₐ[ℂ] ℂ × ℂ :=
  StarAlgHom.prod (StarAlgHom.id ℂ ℂ) (StarAlgHom.id ℂ ℂ)

theorem diagonal_apply (z : ℂ) : diagonal z = (z, z) := rfl

/-- Both coordinate traces restrict to the trace of `ℂ`, so restriction is not injective. -/
theorem not_isUniformTracialCompletion_diagonal_univ :
    ¬ IsUniformTracialCompletion diagonal (Set.univ : Set (TracialState (ℂ × ℂ))) := by
  intro h
  obtain ⟨σ, -, huniq⟩ := h.existsUnique_restrict complexTracialState
  have h1 := huniq fstTrace ⟨Set.mem_univ _, fun a ↦ (tracialState_complex_apply _ a).symm⟩
  have h2 := huniq sndTrace ⟨Set.mem_univ _, fun a ↦ (tracialState_complex_apply _ a).symm⟩
  have h3 : (1 : ℂ) = 0 :=
    congrArg (fun τ : TracialState (ℂ × ℂ) ↦ τ.toLinearMap ((1, 0) : ℂ × ℂ)) (h1.trans h2.symm)
  exact one_ne_zero h3

/-- `(1, -1)` stays at `‖·‖_{2,{midTrace}}`-distance at least `1` from the diagonal. -/
theorem not_isUniformTracialCompletion_diagonal_midTrace :
    ¬ IsUniformTracialCompletion diagonal ({midTrace} : Set (TracialState (ℂ × ℂ))) := by
  intro h
  obtain ⟨x, hx⟩ := h.dense ((1 : ℂ), (-1 : ℂ))
  have hge : ∀ k, 1 ≤ uniformTwoNorm ({midTrace} : Set (TracialState (ℂ × ℂ)))
      (((1 : ℂ), (-1 : ℂ)) - diagonal (x k)) := by
    intro k
    rw [uniformTwoNorm, Set.image_singleton, csSup_singleton, diagonal_apply]
    show 1 ≤ Real.sqrt ((((1 / 2 : ℝ) : ℂ) * (star (1 - x k) * (1 - x k)) +
      ((1 - 1 / 2 : ℝ) : ℂ) * (star (-1 - x k) * (-1 - x k))).re)
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, re_star_mul_self,
      re_star_mul_self, Complex.normSq_apply, Complex.normSq_apply]
    refine (le_of_eq Real.sqrt_one.symm).trans (Real.sqrt_le_sqrt ?_)
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.neg_re,
      Complex.neg_im]
    nlinarith [mul_self_nonneg (x k).re, mul_self_nonneg (x k).im]
  exact absurd (ge_of_tendsto' hx hge) (by norm_num)

end

end ModelTests
end STWProblemXXII
