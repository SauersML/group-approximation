import GroupApproximation.KirchbergAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Cuntz's criterion for pure infiniteness

Cuntz's criterion (Rørdam, *Classification of nuclear C⋆-algebras*, Proposition 4.1.1): a unital
C⋆-algebra with a nonzero non-invertible element, in which `x a y = 1` is solvable for every
`a ≠ 0`, is purely infinite simple. (For C⋆-algebras the first hypothesis is Rørdam's `A ≠ ℂ`, by
Gelfand–Mazur; here it is kept in the elementary form.)

The proof. A nonzero hereditary subalgebra `H` contains a nonzero self-adjoint non-invertible `c`:
take `c = b⋆b` for `0 ≠ b ∈ H`, unless `b⋆b` is invertible, in which case `1 ∈ H`, so `H = A`, and
`c = a⋆a` or `c = aa⋆` for a nonzero non-invertible `a`. Solve `x c y = 1` and put `s = c y`. Then
`1 = s⋆x⋆xs ≤ ‖x‖² s⋆s`, so `s⋆s` is invertible, and `v = s (s⋆s)^{-1/2}` is an isometry whose range
projection `v v⋆ = c (⋯) c` lies in `H`. Since `c` is not invertible, `v v⋆ ≠ 1`, and the partial
isometry `v (v v⋆)` exhibits `v v⋆` as an infinite projection.

The order is the spectral order `CStarAlgebra.spectralOrder`, used only inside proofs.
-/

namespace GroupApproximation
namespace KirchbergAlgebra

universe u

variable {A : Type u} [CStarAlgebra A]

/-- The range projection of a non-unitary isometry is an infinite projection. -/
theorem isInfiniteProjection_mul_star_of_isometry {v : A} (hv : star v * v = 1)
    (hv' : v * star v ≠ 1) : IsInfiniteProjection (v * star v) := by
  have hv2 : ∀ z : A, star v * (v * z) = z := fun z => by rw [← mul_assoc, hv, one_mul]
  have hproj : IsStarProjection (v * star v) :=
    { isIdempotentElem := by
        show v * star v * (v * star v) = v * star v
        simp only [mul_assoc, hv2]
      isSelfAdjoint := IsSelfAdjoint.mul_star_self v }
  refine ⟨hproj, v * (v * star v), ?_, ?_, ?_⟩
  · simp only [star_mul, star_star, mul_assoc, hv2]
  · simp only [star_mul, star_star, mul_assoc, hv2]
  · intro h
    apply hv'
    have h2 := congrArg (fun z => star v * z * v) h
    simp only [star_mul, star_star, mul_assoc, hv2, hv, mul_one] at h2
    exact h2

/-- A non-unitary isometry is a nonzero non-invertible element. -/
theorem exists_ne_zero_not_isUnit_of_isometry {v : A} (hv : star v * v = 1)
    (hv' : v * star v ≠ 1) : ∃ a : A, a ≠ 0 ∧ ¬ IsUnit a := by
  refine ⟨v, fun h0 => hv' ?_, fun hu => hv' ?_⟩
  · rw [h0, mul_zero] at hv
    rw [h0, zero_mul]
    exact hv
  · have hs : star v = ↑hu.unit⁻¹ := by
      calc star v = star v * (v * ↑hu.unit⁻¹) := by rw [hu.mul_val_inv, mul_one]
        _ = ↑hu.unit⁻¹ := by rw [← mul_assoc, hv, one_mul]
    rw [hs, hu.mul_val_inv]

/-- A nonzero hereditary subalgebra contains a nonzero self-adjoint non-invertible element, once `A`
has a nonzero non-invertible element. -/
theorem exists_mem_isSelfAdjoint_not_isUnit (hnt : ∃ a : A, a ≠ 0 ∧ ¬ IsUnit a)
    {H : NonUnitalStarSubalgebra ℂ A} (hH : IsHereditaryCStarSubalgebra H) (hne : H ≠ ⊥) :
    ∃ c ∈ H, c ≠ 0 ∧ IsSelfAdjoint c ∧ ¬ IsUnit c := by
  obtain ⟨b, hbH, hb0⟩ : ∃ b ∈ H, b ≠ 0 := by
    by_contra hcon
    apply hne
    refine eq_bot_iff.2 fun z hz => NonUnitalStarAlgebra.mem_bot.2 ?_
    by_contra hz0
    exact hcon ⟨z, hz, hz0⟩
  have hcH : star b * b ∈ H := mul_mem (star_mem hbH) hbH
  by_cases hu : IsUnit (star b * b)
  · have h1 : (1 : A) ∈ H := by
      obtain ⟨u, hu'⟩ := hu
      have h2 := hH.2 _ hcH ((↑u⁻¹ : A) * ↑u⁻¹) _ hcH
      rwa [← hu', ← mul_assoc, Units.mul_inv, one_mul, Units.inv_mul] at h2
    have hall : ∀ z : A, z ∈ H := fun z => by
      have h2 := hH.2 1 h1 z 1 h1
      rwa [one_mul, mul_one] at h2
    obtain ⟨a, ha0, hau⟩ := hnt
    by_cases hu₁ : IsUnit (star a * a)
    · refine ⟨a * star a, hall _, (CStarRing.mul_star_self_ne_zero_iff a).2 ha0,
        IsSelfAdjoint.mul_star_self a, fun hu₂ => hau ?_⟩
      exact isUnit_iff_exists_and_exists.2
        ⟨⟨star a * ↑hu₂.unit⁻¹, by rw [← mul_assoc, hu₂.mul_val_inv]⟩,
          ⟨↑hu₁.unit⁻¹ * star a, by rw [mul_assoc, hu₁.val_inv_mul]⟩⟩
    · exact ⟨star a * a, hall _, (CStarRing.star_mul_self_ne_zero_iff a).2 ha0,
        IsSelfAdjoint.star_mul_self a, hu₁⟩
  · exact ⟨star b * b, hcH, (CStarRing.star_mul_self_ne_zero_iff b).2 hb0,
      IsSelfAdjoint.star_mul_self b, hu⟩

section Order

variable [PartialOrder A] [StarOrderedRing A]

/-- If `x s = 1`, then `s⋆s ≥ ‖x‖⁻² · 1`, so `s⋆s` is strictly positive. -/
theorem isStrictlyPositive_star_mul_self_of_mul_eq_one [Nontrivial A] {x s : A}
    (hxs : x * s = 1) : IsStrictlyPositive (star s * s) := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hxs
    exact zero_ne_one hxs
  have hr : (‖x‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
  have h1 := star_left_conjugate_le_conjugate
    (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := x)) s
  rw [← mul_assoc, ← star_mul, mul_assoc, hxs, star_one, one_mul,
    ← Algebra.commutes (‖x‖ ^ 2) (star s), mul_assoc] at h1
  have hunit : IsUnit (algebraMap ℝ A (‖x‖ ^ 2) * (star s * s)) :=
    CStarAlgebra.isUnit_of_le 1 h1
  have hd : IsUnit (star s * s) := by
    have h2 := ((IsUnit.mk0 _ (inv_ne_zero hr)).map (algebraMap ℝ A)).mul hunit
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hr, map_one, one_mul] at h2
  exact hd.isStrictlyPositive (star_mul_self_nonneg s)

/-- A self-adjoint non-invertible `c` in a hereditary subalgebra `H` with `x c y = 1` gives an
infinite projection in `H`. -/
theorem exists_isInfiniteProjection_of_mul_mul_eq_one [Nontrivial A]
    {H : NonUnitalStarSubalgebra ℂ A} (hH : IsHereditaryCStarSubalgebra H) {c : A} (hcH : c ∈ H)
    (hcsa : IsSelfAdjoint c) (hcu : ¬ IsUnit c) {x y : A} (hxy : x * c * y = 1) :
    ∃ p ∈ H, IsInfiniteProjection p := by
  have hxs : x * (c * y) = 1 := by rw [← mul_assoc]; exact hxy
  have hd := isStrictlyPositive_star_mul_self_of_mul_eq_one hxs
  obtain ⟨t, ht, htd⟩ : ∃ t : A, IsSelfAdjoint t ∧ t * (star (c * y) * (c * y)) * t = 1 :=
    ⟨(star (c * y) * (c * y)) ^ (-(1 / 2) : ℝ), IsSelfAdjoint.of_nonneg CFC.rpow_nonneg,
      CFC.conjugate_rpow_neg_one_half _ hd⟩
  have hv : star (c * y * t) * (c * y * t) = 1 := by
    rw [star_mul, ht.star_eq, ← mul_assoc, mul_assoc t (star (c * y)) (c * y)]
    exact htd
  have hq1 : c * y * t * star (c * y * t) ≠ 1 := by
    intro hq
    apply hcu
    have hr : c * (y * t * star (c * y * t)) = 1 := by simpa only [mul_assoc] using hq
    have hl := congrArg star hr
    rw [star_mul, hcsa.star_eq, star_one] at hl
    exact isUnit_iff_exists_and_exists.2 ⟨⟨_, hr⟩, ⟨_, hl⟩⟩
  refine ⟨c * y * t * star (c * y * t), ?_, isInfiniteProjection_mul_star_of_isometry hv hq1⟩
  have h3 : c * y * t * star (c * y * t) = c * (y * t * star (y * t)) * c := by
    simp only [star_mul, hcsa.star_eq, mul_assoc]
  rw [h3]
  exact hH.2 c hcH _ c hcH

end Order

/-- **Cuntz's criterion** (Rørdam, Proposition 4.1.1): a unital C⋆-algebra with a nonzero
non-invertible element, in which `x a y = 1` is solvable for every `a ≠ 0`, is purely infinite
simple. -/
theorem isPurelyInfiniteSimple_of_forall_exists_mul_mul_eq_one
    (hnt : ∃ a : A, a ≠ 0 ∧ ¬ IsUnit a) (h : ∀ a : A, a ≠ 0 → ∃ x y : A, x * a * y = 1) :
    IsPurelyInfiniteSimple A := by
  haveI : Nontrivial A := by
    obtain ⟨a, ha, -⟩ := hnt
    exact nontrivial_of_ne a 0 ha
  refine ⟨inferInstance, isSimpleCStar_of_forall_exists_mul_mul_eq_one h, fun H hH hne => ?_⟩
  obtain ⟨c, hcH, hc0, hcsa, hcu⟩ := exists_mem_isSelfAdjoint_not_isUnit hnt hH hne
  obtain ⟨x, y, hxy⟩ := h c hc0
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact exists_isInfiniteProjection_of_mul_mul_eq_one hH hcH hcsa hcu hxy

/-- Cuntz's criterion with a non-unitary isometry as the non-invertible element. -/
theorem isPurelyInfiniteSimple_of_isometry {v : A} (hv : star v * v = 1) (hv' : v * star v ≠ 1)
    (h : ∀ a : A, a ≠ 0 → ∃ x y : A, x * a * y = 1) : IsPurelyInfiniteSimple A :=
  isPurelyInfiniteSimple_of_forall_exists_mul_mul_eq_one
    (exists_ne_zero_not_isUnit_of_isometry hv hv') h

end KirchbergAlgebra
end GroupApproximation
