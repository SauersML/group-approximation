import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosCPBasics

/-!
# Choi–Effros lifting, normalization of a completely positive lift

Lane `TWWSchafhauser-3a` (work order `WO-TWWCore-3`, piece 3a).

Let `π : B → C` be a surjective `⋆`-homomorphism of unital C⋆-algebras and
`φ : A → C` a linear map with `‖φ 1‖ ≤ 1`.  If `φ` has *some* completely positive
lift `L : A → B`, then it has a completely positive *contractive* lift.  The
element `b = L 1 ≥ 0` has `‖π b‖ = ‖φ 1‖ ≤ 1`; compress `L` by
`c = g(b)` with `g(t) = (max 1 t)^{-1/2}`:

* `c⋆ L(1) c = (g · id · g)(b)` has spectrum in `[0, 1]`, so the compression is a
  completely positive map with `‖ψ 1‖ ≤ 1`, hence contractive
  (`norm_apply_le_of_norm_map_one_le`);
* `π c = g(π b) = 1`, because `g ≡ 1` on the spectrum of `π b ⊆ [0, 1]`, so the
  compression is still a lift.

This is the normalization step of Choi–Effros; see M.-D. Choi, E. G. Effros,
*The completely positive lifting problem for C⋆-algebras*, Ann. of Math. (2)
**104** (1976), 585–609, Lemma 3.9, and N. P. Brown, N. Ozawa,
*C⋆-algebras and finite-dimensional approximations*, proof of Theorem C.3.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

universe u v w

/-! ## The normalizing function -/

/-- The normalizing function `t ↦ (max 1 t)^{-1/2}`. -/
def liftNormalizer (t : ℝ) : ℝ := (Real.sqrt (max 1 t))⁻¹

theorem continuous_liftNormalizer : Continuous liftNormalizer := by
  have hsqrt : Continuous fun t : ℝ ↦ Real.sqrt (max 1 t) :=
    Real.continuous_sqrt.comp (continuous_const.max continuous_id)
  have hpos : ∀ t : ℝ, Real.sqrt (max 1 t) ≠ 0 := fun t ↦
    (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos (le_max_left 1 t))).ne'
  exact hsqrt.inv₀ hpos

theorem liftNormalizer_eq_one {t : ℝ} (ht : t ≤ 1) : liftNormalizer t = 1 := by
  unfold liftNormalizer
  rw [max_eq_left ht, Real.sqrt_one, inv_one]

theorem liftNormalizer_mul_mul_eq (t : ℝ) :
    liftNormalizer t * t * liftNormalizer t = t / max 1 t := by
  have hm : 0 < max 1 t := lt_of_lt_of_le one_pos (le_max_left 1 t)
  have hs : Real.sqrt (max 1 t) * Real.sqrt (max 1 t) = max 1 t :=
    Real.mul_self_sqrt hm.le
  calc liftNormalizer t * t * liftNormalizer t
      = t / (Real.sqrt (max 1 t) * Real.sqrt (max 1 t)) := by
        unfold liftNormalizer
        ring
    _ = t / max 1 t := by rw [hs]

theorem norm_liftNormalizer_mul_mul_le {t : ℝ} (ht : 0 ≤ t) :
    ‖liftNormalizer t * t * liftNormalizer t‖ ≤ 1 := by
  have hm : 0 < max 1 t := lt_of_lt_of_le one_pos (le_max_left 1 t)
  rw [liftNormalizer_mul_mul_eq, Real.norm_of_nonneg (div_nonneg ht hm.le)]
  exact (div_le_one hm).mpr (le_max_right 1 t)

/-! ## Normalizing a completely positive lift -/

/-- **A completely positive lift can be made contractive.**  If a linear map
`φ : A → C` with `‖φ 1‖ ≤ 1` has a completely positive lift through the
surjection `π : B → C`, then it has a completely positive contractive lift.
(Surjectivity of `π` is not used here.) -/
theorem exists_cpc_lift_of_cp_lift {A : Type u} {B : Type v} {C : Type w}
    [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    (π : B →⋆ₐ[ℂ] C) {φ : A →ₗ[ℂ] C} (hφ1 : ‖φ 1‖ ≤ 1)
    {L : A →ₗ[ℂ] B} (hL : CStarExactness.IsCompletelyPositive L)
    (hLφ : ∀ a, π (L a) = φ a) :
    ∃ ψ : A →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive ψ ∧
      (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧ ∀ a, π (ψ a) = φ a := by
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  letI : PartialOrder C := CStarAlgebra.spectralOrder C
  letI : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  obtain ⟨y, hy⟩ := exists_map_star_mul_self_eq hL (1 : A)
  rw [star_one, one_mul] at hy
  have hsa : IsSelfAdjoint (L 1) := by
    rw [hy]
    exact IsSelfAdjoint.star_mul_self y
  have hnn : 0 ≤ L 1 := by
    rw [hy]
    exact star_mul_self_nonneg y
  have hg : ContinuousOn liftNormalizer (spectrum ℝ (L 1)) :=
    continuous_liftNormalizer.continuousOn
  have hgid : ContinuousOn (fun t : ℝ ↦ liftNormalizer t * t) (spectrum ℝ (L 1)) :=
    (continuous_liftNormalizer.mul continuous_id').continuousOn
  have hcsa : IsSelfAdjoint (cfc liftNormalizer (L 1)) :=
    cfc_predicate liftNormalizer (L 1)
  -- the compressed unit is a function of `L 1`
  have h1 : cfc (fun t : ℝ ↦ liftNormalizer t * t * liftNormalizer t) (L 1) =
      cfc (fun t : ℝ ↦ liftNormalizer t * t) (L 1) * cfc liftNormalizer (L 1) :=
    cfc_mul (fun t : ℝ ↦ liftNormalizer t * t) liftNormalizer (L 1) hgid hg
  have h2 : cfc (fun t : ℝ ↦ liftNormalizer t * t) (L 1) =
      cfc liftNormalizer (L 1) * cfc (fun t : ℝ ↦ t) (L 1) :=
    cfc_mul liftNormalizer (fun t : ℝ ↦ t) (L 1) hg (continuousOn_id' _)
  have hone : compressLinearMap (cfc liftNormalizer (L 1)) L 1 =
      cfc (fun t : ℝ ↦ liftNormalizer t * t * liftNormalizer t) (L 1) := by
    rw [compressLinearMap_apply, hcsa.star_eq, h1, h2, cfc_id' ℝ (L 1) hsa]
  have hnorm1 : ‖compressLinearMap (cfc liftNormalizer (L 1)) L 1‖ ≤ 1 := by
    rw [hone]
    exact norm_cfc_le zero_le_one fun x hx ↦
      norm_liftNormalizer_mul_mul_le (spectrum_nonneg_of_nonneg hnn hx)
  -- the normalizer is invisible in the quotient
  have hπcont : Continuous π :=
    AddMonoidHomClass.continuous_of_bound π 1 fun b ↦
      (NonUnitalStarAlgHom.norm_apply_le π b).trans_eq (one_mul _).symm
  have hπsa : IsSelfAdjoint (π (L 1)) := hsa.map π
  have hπnn : 0 ≤ π (L 1) := by
    rw [hy, map_mul, map_star]
    exact star_mul_self_nonneg _
  have hle : π (L 1) ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (π (L 1)) hπnn).mp (by
      rw [hLφ]
      exact hφ1)
  have heqOn : (spectrum ℝ (π (L 1))).EqOn liftNormalizer (fun _ ↦ 1) := fun x hx ↦
    liftNormalizer_eq_one ((CFC.le_one_iff (R := ℝ) (π (L 1)) hπsa).mp hle x hx)
  have hπc : π (cfc liftNormalizer (L 1)) = 1 := by
    rw [StarAlgHom.map_cfc π liftNormalizer (L 1) hg hπcont hsa hπsa,
      cfc_congr heqOn, cfc_const_one ℝ (π (L 1)) hπsa]
  have hψ := isCompletelyPositive_compressLinearMap (cfc liftNormalizer (L 1)) hL
  refine ⟨compressLinearMap (cfc liftNormalizer (L 1)) L, hψ,
    norm_apply_le_of_norm_map_one_le hψ hnorm1, fun a ↦ ?_⟩
  rw [compressLinearMap_apply, map_mul, map_mul, map_star, hπc, star_one, one_mul,
    mul_one, hLφ]

end

end TWWSchafhauser
end Full
end GroupApproximation
