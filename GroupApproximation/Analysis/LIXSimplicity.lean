import GroupApproximation.Analysis.CStarExactnessSliceReduction
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Simplicity of a unital increasing union whose stages become full

Let `B` be a unital C⋆-algebra which is the closure of an increasing union of closed unital
⋆-subalgebras `S i`.  This module proves that `B` is simple — every nonzero closed ⋆-stable
two-sided ideal is all of `B` — as soon as every nonzero positive element of every stage is
*full* in `B`.

That is the structural half of the argument for STW Problem LIX.  The twisted AH tower there is
built so that a point-evaluation summand at a later stage makes every nonzero positive element
of an earlier stage full, and simplicity of the limit is what turns a finite-stage
non-null-homotopic unitary into a statement about *simple* C⋆-algebras.  Nothing below mentions
that tower: the theorem is unconditional and about an arbitrary increasing union.

## What is proved

* `cfc_mem_of_isClosed` — a closed ⋆-subalgebra of a C⋆-algebra is closed under the continuous
  functional calculus of its selfadjoint elements.  Spectral permanence is not needed: the
  function is asked to be continuous everywhere, so the calculus computed inside the subalgebra
  transports along the inclusion by `StarAlgHomClass.map_cfc`.
* `exists_ge_nonneg_mem_approx` — a positive element of `B` is approximated, to any accuracy, by
  a *positive* element of an arbitrarily late stage.  This is "positive stage approximations
  exist by approximating `b^{1/2}` and then taking the product with its adjoint".
* `exists_ge_mem_ideal_of_nonneg` — a nonzero closed ⋆-stable two-sided ideal meets some stage
  in a nonzero positive element.  This is the step that must not be skipped: an approximant of
  an element of the ideal need not itself lie in the ideal.  What repairs that is the cut
  `c = (a - ‖b‖/4)₊`, which the quotient kills because `‖π a‖ < ‖b‖/8`, and which is nonzero
  because `‖a‖ > 7‖b‖/8` lies in the spectrum of `a`.
* `eq_top_of_stagewise_full` — the simplicity theorem.

## Why the ideal is asked to be ⋆-stable

Every closed two-sided ideal of a C⋆-algebra is automatically ⋆-stable, but that theorem — which
runs through an approximate unit of the ideal — is not proved here, and asking for ⋆-stability
costs the application nothing, since it is what the C⋆-quotient of
`Analysis/CStarIdealApproximateUnit` consumes anyway.  The hypothesis is therefore stated rather
than smuggled: `eq_top_of_stagewise_full` concludes about ⋆-stable ideals only.
-/

namespace GroupApproximation

namespace LIX

open CStarTensor

noncomputable section

/-! ### The cut function -/

/-- The cut `t ↦ (t - r)₊`.  Applied through the functional calculus to a positive `a`, it
kills the part of the spectrum below `r` and leaves the rest strictly positive. -/
def posCut (r : ℝ) : ℝ → ℝ := fun t => max (t - r) 0

theorem continuous_posCut (r : ℝ) : Continuous (posCut r) :=
  (continuous_id.sub continuous_const).max continuous_const

theorem posCut_nonneg (r t : ℝ) : 0 ≤ posCut r t := le_max_right _ _

theorem posCut_eq_zero {r t : ℝ} (h : t ≤ r) : posCut r t = 0 := max_eq_right (sub_nonpos.mpr h)

theorem posCut_pos {r t : ℝ} (h : r < t) : 0 < posCut r t :=
  lt_max_iff.mpr (Or.inl (by linarith))

/-! ### A closed ⋆-subalgebra absorbs the continuous functional calculus -/

section Subalgebra

variable {B : Type*} [CStarAlgebra B]

/-- A closed ⋆-subalgebra of a C⋆-algebra contains `cfc f a` whenever it contains the selfadjoint
element `a` and `f` is continuous.  The calculus computed in the subalgebra — itself a
C⋆-algebra — maps to the calculus computed in `B` along the inclusion. -/
theorem cfc_mem_of_isClosed {T : StarSubalgebra ℂ B} (hT : IsClosed (T : Set B))
    {f : ℝ → ℝ} (hf : Continuous f) {a : B} (ha : a ∈ T) (ha' : IsSelfAdjoint a) :
    cfc f a ∈ T := by
  haveI : IsClosed (T : Set B) := hT
  have hsa : IsSelfAdjoint (⟨a, ha⟩ : T) := Subtype.ext ha'
  have hcont : Continuous (T.subtype : T → B) := by
    rw [StarSubalgebra.coe_subtype]
    exact continuous_subtype_val
  have hmap : (T.subtype (cfc f (⟨a, ha⟩ : T)) : B) = cfc f a :=
    StarAlgHomClass.map_cfc (S := ℂ) T.subtype f (⟨a, ha⟩ : T) hf.continuousOn hcont hsa ha'
  rw [← hmap]
  exact (cfc f (⟨a, ha⟩ : T)).2

end Subalgebra

/-! ### Fullness -/

section Full

variable {B : Type*} [CStarAlgebra B]

/-- `a` is **full** in `B`: the closed two-sided ideal it generates is all of `B`.  Stated
concretely, so that no ideal-generation API is involved — `1` is a limit of finite sums
`∑ xᵢ a yᵢ`. -/
def IsFull (a : B) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (x y : Fin n → B), ‖1 - ∑ i, x i * a * y i‖ < ε

/-- A full element of a closed two-sided ideal forces the ideal to contain the unit. -/
theorem one_mem_of_isFull {I : Ideal B} [I.IsTwoSided] (hI : IsClosed (I : Set B))
    {a : B} (ha : a ∈ I) (hfull : IsFull a) : (1 : B) ∈ I := by
  have h1 : (1 : B) ∈ closure (I : Set B) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, x, y, hxy⟩ := hfull ε hε
    refine ⟨∑ i, x i * a * y i, ?_, ?_⟩
    · exact SetLike.mem_coe.mpr
        (sum_mem fun i _ => Ideal.mul_mem_right _ I (Ideal.mul_mem_left I _ ha))
    · rwa [dist_eq_norm]
  rwa [hI.closure_eq] at h1

end Full

/-! ### Positive approximation inside a stage -/

section Approx

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {ι : Type*} [SemilatticeSup ι] {S : ι → StarSubalgebra ℂ B}

/-- A positive element of `B` is approximated, to any accuracy, by a positive element of an
arbitrarily late stage: approximate its square root by an element `z` of the dense union and
take `z⋆ z`, positive by construction and close to `(√b)⋆ √b = b`. -/
theorem exists_ge_nonneg_mem_approx (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    (k : ι) {b : B} (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, k ≤ j ∧ ∃ a : B, a ∈ S j ∧ 0 ≤ a ∧ ‖a - b‖ < ε := by
  obtain ⟨s, hs0, hss⟩ : ∃ s : B, 0 ≤ s ∧ s * s = b :=
    ⟨CFC.sqrt b, CFC.sqrt_nonneg b, CFC.sqrt_mul_sqrt_self b hb⟩
  have hsa : star s = s := (IsSelfAdjoint.of_nonneg hs0).star_eq
  have hCpos : (0 : ℝ) < 2 * (‖s‖ + 1) := by positivity
  obtain ⟨δ, hδ0, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 2 * (‖s‖ + 1) * δ ≤ ε := by
    refine ⟨min 1 (ε / (2 * (‖s‖ + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    have hle : min 1 (ε / (2 * (‖s‖ + 1))) ≤ ε / (2 * (‖s‖ + 1)) := min_le_right _ _
    have hEq : 2 * (‖s‖ + 1) * (ε / (2 * (‖s‖ + 1))) = ε := by field_simp
    calc 2 * (‖s‖ + 1) * min 1 (ε / (2 * (‖s‖ + 1)))
        ≤ 2 * (‖s‖ + 1) * (ε / (2 * (‖s‖ + 1))) := mul_le_mul_of_nonneg_left hle hCpos.le
      _ = ε := hEq
  obtain ⟨z, hz₁, hz₂⟩ := Metric.dense_iff.mp hdense s δ hδ0
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz₂
  have hzS : z ∈ S (k ⊔ i) := hmono le_sup_right hzi
  have hzd : ‖z - s‖ < δ := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hz₁
  have hzn : ‖z‖ ≤ ‖s‖ + δ := by
    have h : ‖z‖ ≤ ‖s‖ + ‖z - s‖ := by simpa using norm_add_le s (z - s)
    linarith
  refine ⟨k ⊔ i, le_sup_left, star z * z, mul_mem (star_mem hzS) hzS,
    star_mul_self_nonneg z, ?_⟩
  have key : star z * z - b = star z * (z - s) + star (z - s) * s := by
    rw [← hss, star_sub, hsa]
    ring
  have hnn : (0 : ℝ) ≤ ‖z - s‖ := norm_nonneg _
  have hsn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
  calc ‖star z * z - b‖
      ≤ ‖star z * (z - s)‖ + ‖star (z - s) * s‖ := by
        rw [key]; exact norm_add_le _ _
    _ ≤ ‖star z‖ * ‖z - s‖ + ‖star (z - s)‖ * ‖s‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = (‖z‖ + ‖s‖) * ‖z - s‖ := by rw [norm_star, norm_star]; ring
    _ ≤ 2 * (‖s‖ + 1) * ‖z - s‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hnn
    _ < 2 * (‖s‖ + 1) * δ := mul_lt_mul_of_pos_left hzd hCpos
    _ ≤ ε := hδε

end Approx

/-! ### A nonzero ideal meets a stage -/

section Ideal

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial B]
variable {ι : Type*} [SemilatticeSup ι] {S : ι → StarSubalgebra ℂ B}

/-- **A nonzero closed ⋆-stable two-sided ideal meets some stage in a nonzero positive element.**

The approximant `a ∈ S j` of a positive `b ∈ I` need not itself lie in `I`; the cut
`c = (a - ‖b‖/4)₊` repairs that.  In the quotient `‖π a‖ = ‖π (a - b)‖ ≤ ‖a - b‖ < ‖b‖/8`, so
the spectrum of `π a` lies below `‖b‖/4` and `π c = 0`.  On the other side
`‖a‖ > 7‖b‖/8 > ‖b‖/4` lies in the spectrum of `a`, so the spectrum of `c` contains a strictly
positive point. -/
theorem exists_ge_mem_ideal_of_nonneg (hclosed : ∀ i, IsClosed (S i : Set B))
    (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    {I : Ideal B} [I.IsTwoSided] [IsStarStable I] (hIclosed : IsClosed (I : Set B))
    {b : B} (hbI : b ∈ I) (hb0 : 0 ≤ b) (hbne : b ≠ 0) (k : ι) :
    ∃ j, k ≤ j ∧ ∃ c : B, c ∈ S j ∧ c ∈ I ∧ 0 ≤ c ∧ c ≠ 0 := by
  haveI : IsClosed (I : Set B) := hIclosed
  have hM : 0 < ‖b‖ := norm_pos_iff.mpr hbne
  obtain ⟨j, hkj, a, haS, ha0, haε⟩ :=
    exists_ge_nonneg_mem_approx hmono hdense k hb0 (by linarith : (0 : ℝ) < ‖b‖ / 8)
  have hasa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  have hfc : Continuous (posCut (‖b‖ / 4)) := continuous_posCut _
  refine ⟨j, hkj, cfc (posCut (‖b‖ / 4)) a,
    cfc_mem_of_isClosed (hclosed j) hfc haS hasa, ?_, ?_, ?_⟩
  · -- membership in the ideal: the cut dies in the quotient
    have hπa : IsSelfAdjoint ((quotientStarMk I) a) := by
      show star ((quotientStarMk I) a) = (quotientStarMk I) a
      rw [← map_star, hasa.star_eq]
    have hπb : (quotientStarMk I) b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hbI
    have hπnorm : ‖(quotientStarMk I) a‖ < ‖b‖ / 8 := by
      have h1 : (quotientStarMk I) a = (quotientStarMk I) (a - b) := by
        rw [map_sub, hπb, sub_zero]
      rw [h1]
      exact lt_of_le_of_lt (quotient_norm_mk_le I (a - b)) haε
    have hcongr : Set.EqOn (posCut (‖b‖ / 4)) (fun _ : ℝ => (0 : ℝ))
        (spectrum ℝ ((quotientStarMk I) a)) := by
      intro t ht
      have htle : |t| ≤ ‖(quotientStarMk I) a‖ := by
        simpa using spectrum.norm_le_norm_of_mem ht
      have h2 : t ≤ |t| := le_abs_self t
      exact posCut_eq_zero (by linarith)
    have hzero : cfc (posCut (‖b‖ / 4)) ((quotientStarMk I) a) = 0 := by
      rw [cfc_congr hcongr, cfc_const_zero]
    have hmapped : (quotientStarMk I) (cfc (posCut (‖b‖ / 4)) a) = 0 := by
      rw [StarAlgHomClass.map_cfc (S := ℂ) (quotientStarMk I) (posCut (‖b‖ / 4)) a
        hfc.continuousOn (continuous_quotientStarMk I) hasa hπa]
      exact hzero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmapped
  · exact cfc_nonneg fun t _ => posCut_nonneg _ t
  · -- nonvanishing: `‖a‖` survives the cut
    have hnorm : ‖b‖ - ‖b‖ / 8 < ‖a‖ := by
      have h := norm_sub_norm_le b a
      have h2 : ‖b - a‖ = ‖a - b‖ := norm_sub_rev _ _
      rw [h2] at h
      linarith
    have hmem : ‖a‖ ∈ spectrum ℝ a := CStarAlgebra.norm_mem_spectrum_of_nonneg ha0
    have hcutpos : 0 < posCut (‖b‖ / 4) ‖a‖ := posCut_pos (by linarith)
    intro hc
    have hspec : posCut (‖b‖ / 4) ‖a‖ ∈ spectrum ℝ (cfc (posCut (‖b‖ / 4)) a) := by
      rw [cfc_map_spectrum hasa hfc.continuousOn]
      exact ⟨‖a‖, hmem, rfl⟩
    rw [hc, spectrum.zero_eq] at hspec
    simp only [Set.mem_singleton_iff] at hspec
    exact absurd hspec (ne_of_gt hcutpos)

/-! ### Simplicity -/

/-- **Simplicity of a unital increasing union whose stages become full.**

If `B` is the closure of an increasing union of closed unital ⋆-subalgebras `S i`, and every
nonzero positive element of every stage is full in `B`, then every nonzero closed ⋆-stable
two-sided ideal of `B` is all of `B`.

The fullness hypothesis is exactly what a later-stage point-evaluation summand supplies in an AH
tower: an element full in a later *stage* is a fortiori full in `B`, the same finite sums
witnessing it. -/
theorem eq_top_of_stagewise_full [Nonempty ι] (hclosed : ∀ i, IsClosed (S i : Set B))
    (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    (hfull : ∀ (i : ι) (a : B), a ∈ S i → 0 ≤ a → a ≠ 0 → IsFull a)
    {I : Ideal B} [I.IsTwoSided] [IsStarStable I] (hIclosed : IsClosed (I : Set B))
    {x : B} (hxI : x ∈ I) (hx : x ≠ 0) :
    I = ⊤ := by
  have hb0 : (0 : B) ≤ star x * x := star_mul_self_nonneg x
  have hbI : star x * x ∈ I := Ideal.mul_mem_left I _ hxI
  have hbne : star x * x ≠ 0 := (CStarRing.star_mul_self_ne_zero_iff x).mpr hx
  obtain ⟨j, -, c, hcS, hcI, hc0, hcne⟩ :=
    exists_ge_mem_ideal_of_nonneg hclosed hmono hdense hIclosed hbI hb0 hbne
      (Classical.arbitrary ι)
  exact (Ideal.eq_top_iff_one I).mpr (one_mem_of_isFull hIclosed hcI (hfull j c hcS hc0 hcne))

end Ideal

end

end LIX

end GroupApproximation
