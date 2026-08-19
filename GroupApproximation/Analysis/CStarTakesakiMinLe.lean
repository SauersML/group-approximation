import GroupApproximation.Analysis.CStarTakesakiDense
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The hard half of Takesaki's identification: `‖·‖_min ≤ ‖·‖_{π,ρ}`

## The statement

For unital C⋆-algebras `A`, `B` and *faithful* unital ⋆-representations
`π₀ : A → B(H)`, `ρ₀ : B → B(K)` on complete Hilbert spaces, the canonical
minimal tensor norm of `CStarMinTensorNorm` is dominated by the spatial norm
of the pair:

`minTensorNorm x ≤ spatialNorm (ofStarAlgHom π₀) (ofStarAlgHom ρ₀) x`.

This is the direction of Takesaki's theorem that the textbook proof obtains
from weak-⋆ density of vector states of a faithful representation (Fell's
theorem) --- the analytically serious half.  With it, the supremum defining
`‖·‖_min` is *attained-or-approached inside any single faithful pair*, which
is what lets `⊗_min` be computed in concrete representations.

## The proof, and why no weak-⋆ topology appears

Fix a state pair `(φ, ψ)`.  The spatial operator of the GNS pair at `x` has
its norm computed on the dense span of coefficient vectors
`w = Σⱼ π_φ(aⱼ)Ω ⊗ ηⱼ` (`CStarTakesakiDense`).  At such a vector, by the
coefficient identity (`CStarTakesakiCoefficient`),

`‖(π_φ ⊗ ρ)(x) w‖² = re φ(z₂)`  and  `‖w‖² = re φ(z₁)`,

where `z₁ = leftSlice ρ a η 1` and `z₂ = leftSlice ρ a η (x⋆x)` are single
elements of `A`.  The *same* identity read in the faithful representation
`π₀` shows that the selfadjoint element `r = c² • z₁ - z₂`, where `c` is the
spatial norm of the pair `(π₀, ρ)` at `x`, has nonnegative quadratic form in
`π₀`; the numerical-range bound and the isometry of `π₀` turn this into
`‖‖r‖•1 - r‖ ≤ ‖r‖` in `A`, and the positivity transfer then gives
`re φ(r) ≥ 0` for the state `φ` --- that is, `re φ(z₂) ≤ c² · re φ(z₁)`,
i.e. `‖(π_φ ⊗ ρ)(x) w‖ ≤ c ‖w‖`.  So each GNS leg is dominated by the
faithful leg, one factor at a time, and the supremum over state pairs
follows.  Fell's density theorem is replaced by the positivity transfer,
which is an exact inequality, not an approximation.

## What this does and does not close

This module proves one half of Takesaki's identification (Stage C.4 of the
tensor-lane roadmap): the minimal norm is dominated by every faithful
spatial norm.  The converse domination --- every spatial norm is dominated
by the minimal norm --- is geometrically different (cyclic decomposition of
an arbitrary representation) and is not claimed here; until it lands, the
identification is an inequality, not an equality, and no manuscript row
changes grade.  `SO.16` and `RE.05` remain as recorded.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped InnerProductSpace TensorProduct

universe u v w x

/-! ## The C⋆ massage: quadratic forms of `x⋆x` are squared norms -/

section Massage

variable {A : Type u} {B : Type v} [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} {K : Type x} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The quadratic form of a product representation at `x⋆x` is the squared
norm of the image of `x`: the adjoint relation of the ⋆-representation, in
inner-product form. -/
theorem inner_spatialHom_star_mul_self (π : StarRep A H) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) (W : H ⊗[ℂ] K) :
    ⟪W, spatialHom π ρ (star x * x) W⟫_ℂ
      = ⟪spatialHom π ρ x W, spatialHom π ρ x W⟫_ℂ := by
  have m1 : spatialHom π ρ (star x * x) W
      = spatialHom π ρ (star x) (spatialHom π ρ x W) := by
    rw [map_mul, mul_eq_comp, ContinuousLinearMap.comp_apply]
  have m2 := (spatialRep π ρ).isAdjoint_star x W (spatialHom π ρ x W)
  rw [m1]
  exact m2.symm

end Massage

/-! ## Leg one: the first GNS factor is dominated by a faithful factor -/

section LegLeft

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable {B : Type v} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Left-leg domination.**  For a faithful unital ⋆-representation `π₀`
of `A` on a complete Hilbert space and *any* ⋆-representation `ρ` of `B`,
every GNS first leg is dominated:
`spatialNorm (gns φ) ρ x ≤ spatialNorm π₀ ρ x`. -/
theorem spatialNorm_gnsRep_le_left (π₀ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ₀ : Function.Injective π₀) (φ : State A) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) :
    spatialNorm φ.gnsRep ρ x
      ≤ spatialNorm (StarRep.ofStarAlgHom π₀) ρ x := by
  set c := spatialNorm (StarRep.ofStarAlgHom π₀) ρ x with hc_def
  have hc0 : 0 ≤ c := (spatialNorm_isCStarSeminorm _ _).nonneg x
  have hcn : c = ‖spatialHom (StarRep.ofStarAlgHom π₀) ρ x‖ := by
    rw [hc_def, spatialNorm_apply]
  rw [spatialNorm_apply]
  refine opNorm_le_of_dense _ (dense_gnsCoeffSpan φ) hc0 ?_
  intro w hw
  obtain ⟨n, a, η, rfl⟩ := exists_coeffVector_of_mem_gnsCoeffSpan φ hw
  -- the two slice elements and the comparison element `r`
  have hz₂star : star (leftSlice ρ a η (star x * x))
      = leftSlice ρ a η (star x * x) := by
    rw [← leftSlice_star, star_mul, star_star]
  have hz₁star : star (leftSlice ρ a η (1 : A ⊗[ℂ] B))
      = leftSlice ρ a η (1 : A ⊗[ℂ] B) := by
    rw [← leftSlice_star, star_one]
  set z₁ := leftSlice ρ a η (1 : A ⊗[ℂ] B) with hz₁
  set z₂ := leftSlice ρ a η (star x * x) with hz₂
  set r := ((c ^ 2 : ℝ) : ℂ) • z₁ - z₂ with hr_def
  have hstar : star r = r := by
    rw [hr_def, star_sub, star_smul, hz₁star, hz₂star]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal]
  -- the quadratic form of `π₀ r` is nonnegative
  have hπr : ∀ ζ : H,
      0 ≤ (⟪ζ, (StarRep.ofStarAlgHom π₀).hom r ζ⟫_ℂ).re := by
    intro ζ
    have e1 : (StarRep.ofStarAlgHom π₀).hom r
        = ((c ^ 2 : ℝ) : ℂ) • (StarRep.ofStarAlgHom π₀).hom z₁
          - (StarRep.ofStarAlgHom π₀).hom z₂ := by
      rw [hr_def, map_sub, map_smul]
    rw [e1, sub_apply, smul_apply,
      inner_sub_right, inner_smul_right]
    have i₁ : ⟪ζ, (StarRep.ofStarAlgHom π₀).hom z₁ ζ⟫_ℂ
        = ⟪coeffVector (StarRep.ofStarAlgHom π₀) ζ a η,
            coeffVector (StarRep.ofStarAlgHom π₀) ζ a η⟫_ℂ := by
      rw [hz₁]
      exact (inner_coeffVector_self (StarRep.ofStarAlgHom π₀) ρ a η ζ).symm
    have i₂ : ⟪ζ, (StarRep.ofStarAlgHom π₀).hom z₂ ζ⟫_ℂ
        = ⟪coeffVector (StarRep.ofStarAlgHom π₀) ζ a η,
            spatialHom (StarRep.ofStarAlgHom π₀) ρ (star x * x)
              (coeffVector (StarRep.ofStarAlgHom π₀) ζ a η)⟫_ℂ := by
      rw [hz₂]
      exact (inner_coeffVector_spatialHom (StarRep.ofStarAlgHom π₀) ρ a η ζ
        (star x * x)).symm
    rw [i₁, i₂, inner_spatialHom_star_mul_self]
    -- now everything is a norm
    have n1 : (⟪coeffVector (StarRep.ofStarAlgHom π₀) ζ a η,
        coeffVector (StarRep.ofStarAlgHom π₀) ζ a η⟫_ℂ).re
        = ‖coeffVector (StarRep.ofStarAlgHom π₀) ζ a η‖ ^ 2 :=
      re_inner_self _
    have n1im : (⟪coeffVector (StarRep.ofStarAlgHom π₀) ζ a η,
        coeffVector (StarRep.ofStarAlgHom π₀) ζ a η⟫_ℂ).im = 0 :=
      im_inner_self _
    have n2 : (⟪spatialHom (StarRep.ofStarAlgHom π₀) ρ x
          (coeffVector (StarRep.ofStarAlgHom π₀) ζ a η),
        spatialHom (StarRep.ofStarAlgHom π₀) ρ x
          (coeffVector (StarRep.ofStarAlgHom π₀) ζ a η)⟫_ℂ).re
        = ‖spatialHom (StarRep.ofStarAlgHom π₀) ρ x
            (coeffVector (StarRep.ofStarAlgHom π₀) ζ a η)‖ ^ 2 :=
      re_inner_self _
    have hb : ‖spatialHom (StarRep.ofStarAlgHom π₀) ρ x
          (coeffVector (StarRep.ofStarAlgHom π₀) ζ a η)‖
        ≤ c * ‖coeffVector (StarRep.ofStarAlgHom π₀) ζ a η‖ := by
      have h := (spatialHom (StarRep.ofStarAlgHom π₀) ρ x).le_opNorm
        (coeffVector (StarRep.ofStarAlgHom π₀) ζ a η)
      rw [← hcn] at h
      exact h
    rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, n1, n1im, n2]
    nlinarith [norm_nonneg (coeffVector (StarRep.ofStarAlgHom π₀) ζ a η),
      norm_nonneg (spatialHom (StarRep.ofStarAlgHom π₀) ρ x
        (coeffVector (StarRep.ofStarAlgHom π₀) ζ a η)), hb, hc0]
  -- the numerical-range bound in `B(H)`, transferred to `A`
  have hadjr : IsAdjoint ((StarRep.ofStarAlgHom π₀).hom r)
      ((StarRep.ofStarAlgHom π₀).hom r) := by
    have h := (StarRep.ofStarAlgHom π₀).isAdjoint_star r
    rwa [hstar] at h
  have hop := norm_smul_one_sub_le_of_isAdjoint hadjr hπr
  have hiso : ∀ u : A, ‖π₀ u‖ = ‖u‖ := fun u =>
    NonUnitalStarAlgHom.norm_map π₀ hπ₀ u
  have hrA : ‖((‖r‖ : ℂ) • (1 : A)) - r‖ ≤ ‖r‖ := by
    have e2 : π₀ (((‖r‖ : ℂ) • (1 : A)) - r)
        = ((‖r‖ : ℂ) • (1 : H →L[ℂ] H)) - π₀ r := by
      rw [map_sub, map_smul, map_one]
    have e3 : ‖((‖r‖ : ℂ) • (1 : A)) - r‖
        = ‖((‖r‖ : ℂ) • (1 : H →L[ℂ] H)) - π₀ r‖ := by
      rw [← e2, hiso]
    have e4 : ‖π₀ r‖ = ‖r‖ := hiso r
    rw [e3, ← e4]
    exact hop
  -- the state is nonnegative on `r`
  have hstate : 0 ≤ (φ.toCLM r).re :=
    re_apply_nonneg_of_norm_smul_one_sub_le φ.toCLM φ.map_one φ.norm_le hrA
  -- read the state values as norms of the GNS side
  have g1 : ⟪coeffVector φ.gnsRep φ.gnsVector a η,
      spatialHom φ.gnsRep ρ (star x * x)
        (coeffVector φ.gnsRep φ.gnsVector a η)⟫_ℂ = φ.toCLM z₂ := by
    rw [inner_coeffVector_spatialHom φ.gnsRep ρ a η φ.gnsVector
      (star x * x), ← hz₂]
    exact inner_gnsVector_gnsRep φ z₂
  have g2 : ⟪coeffVector φ.gnsRep φ.gnsVector a η,
      coeffVector φ.gnsRep φ.gnsVector a η⟫_ℂ = φ.toCLM z₁ := by
    rw [inner_coeffVector_self φ.gnsRep ρ a η φ.gnsVector, ← hz₁]
    exact inner_gnsVector_gnsRep φ z₁
  have g3 : ‖spatialHom φ.gnsRep ρ x
      (coeffVector φ.gnsRep φ.gnsVector a η)‖ ^ 2 = (φ.toCLM z₂).re := by
    rw [← re_inner_self, ← inner_spatialHom_star_mul_self, g1]
  have g4 : ‖coeffVector φ.gnsRep φ.gnsVector a η‖ ^ 2
      = (φ.toCLM z₁).re := by
    rw [← re_inner_self, g2]
  have g5 : (φ.toCLM r).re
      = c ^ 2 * (φ.toCLM z₁).re - (φ.toCLM z₂).re := by
    rw [hr_def, map_sub, map_smul, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have g6 : ‖spatialHom φ.gnsRep ρ x
      (coeffVector φ.gnsRep φ.gnsVector a η)‖ ^ 2
      ≤ c ^ 2 * ‖coeffVector φ.gnsRep φ.gnsVector a η‖ ^ 2 := by
    rw [g3, g4]
    linarith [hstate, g5.symm.le, g5.le]
  have hnn : 0 ≤ ‖spatialHom φ.gnsRep ρ x
      (coeffVector φ.gnsRep φ.gnsVector a η)‖ := norm_nonneg _
  have hnn2 : 0 ≤ c * ‖coeffVector φ.gnsRep φ.gnsVector a η‖ :=
    mul_nonneg hc0 (norm_nonneg _)
  refine (sq_le_sq₀ hnn hnn2).mp ?_
  have hsq : (c * ‖coeffVector φ.gnsRep φ.gnsVector a η‖) ^ 2
      = c ^ 2 * ‖coeffVector φ.gnsRep φ.gnsVector a η‖ ^ 2 := by ring
  rw [hsq]
  exact g6

end LegLeft

/-! ## Leg two: the second GNS factor is dominated by a faithful factor -/

section LegRight

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {B : Type v} [CStarAlgebra B] [Nontrivial B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- **Right-leg domination.**  For a faithful unital ⋆-representation `ρ₀`
of `B` on a complete Hilbert space and *any* ⋆-representation `π` of `A`,
every GNS second leg is dominated:
`spatialNorm π (gns ψ) x ≤ spatialNorm π ρ₀ x`. -/
theorem spatialNorm_gnsRep_le_right (ρ₀ : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hρ₀ : Function.Injective ρ₀) (ψ : State B) (π : StarRep A H)
    (x : A ⊗[ℂ] B) :
    spatialNorm π ψ.gnsRep x
      ≤ spatialNorm π (StarRep.ofStarAlgHom ρ₀) x := by
  set c := spatialNorm π (StarRep.ofStarAlgHom ρ₀) x with hc_def
  have hc0 : 0 ≤ c := (spatialNorm_isCStarSeminorm _ _).nonneg x
  have hcn : c = ‖spatialHom π (StarRep.ofStarAlgHom ρ₀) x‖ := by
    rw [hc_def, spatialNorm_apply]
  rw [spatialNorm_apply]
  refine opNorm_le_of_dense _ (dense_rightGnsCoeffSpan ψ) hc0 ?_
  intro w hw
  obtain ⟨n, b, ξ, rfl⟩ := exists_rightCoeffVector_of_mem ψ hw
  have hz₂star : star (rightSlice π b ξ (star x * x))
      = rightSlice π b ξ (star x * x) := by
    rw [← rightSlice_star, star_mul, star_star]
  have hz₁star : star (rightSlice π b ξ (1 : A ⊗[ℂ] B))
      = rightSlice π b ξ (1 : A ⊗[ℂ] B) := by
    rw [← rightSlice_star, star_one]
  set z₁ := rightSlice π b ξ (1 : A ⊗[ℂ] B) with hz₁
  set z₂ := rightSlice π b ξ (star x * x) with hz₂
  set r := ((c ^ 2 : ℝ) : ℂ) • z₁ - z₂ with hr_def
  have hstar : star r = r := by
    rw [hr_def, star_sub, star_smul, hz₁star, hz₂star]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal]
  have hρr : ∀ ζ : K,
      0 ≤ (⟪ζ, (StarRep.ofStarAlgHom ρ₀).hom r ζ⟫_ℂ).re := by
    intro ζ
    have e1 : (StarRep.ofStarAlgHom ρ₀).hom r
        = ((c ^ 2 : ℝ) : ℂ) • (StarRep.ofStarAlgHom ρ₀).hom z₁
          - (StarRep.ofStarAlgHom ρ₀).hom z₂ := by
      rw [hr_def, map_sub, map_smul]
    rw [e1, sub_apply, smul_apply,
      inner_sub_right, inner_smul_right]
    have i₁ : ⟪ζ, (StarRep.ofStarAlgHom ρ₀).hom z₁ ζ⟫_ℂ
        = ⟪rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ,
            rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ⟫_ℂ := by
      rw [hz₁]
      exact (inner_rightCoeffVector_self π (StarRep.ofStarAlgHom ρ₀)
        b ξ ζ).symm
    have i₂ : ⟪ζ, (StarRep.ofStarAlgHom ρ₀).hom z₂ ζ⟫_ℂ
        = ⟪rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ,
            spatialHom π (StarRep.ofStarAlgHom ρ₀) (star x * x)
              (rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ)⟫_ℂ := by
      rw [hz₂]
      exact (inner_rightCoeffVector_spatialHom π (StarRep.ofStarAlgHom ρ₀)
        b ξ ζ (star x * x)).symm
    rw [i₁, i₂, inner_spatialHom_star_mul_self]
    have n1 : (⟪rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ,
        rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ⟫_ℂ).re
        = ‖rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ‖ ^ 2 :=
      re_inner_self _
    have n1im : (⟪rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ,
        rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ⟫_ℂ).im = 0 :=
      im_inner_self _
    have n2 : (⟪spatialHom π (StarRep.ofStarAlgHom ρ₀) x
          (rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ),
        spatialHom π (StarRep.ofStarAlgHom ρ₀) x
          (rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ)⟫_ℂ).re
        = ‖spatialHom π (StarRep.ofStarAlgHom ρ₀) x
            (rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ)‖ ^ 2 :=
      re_inner_self _
    have hb : ‖spatialHom π (StarRep.ofStarAlgHom ρ₀) x
          (rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ)‖
        ≤ c * ‖rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ‖ := by
      have h := (spatialHom π (StarRep.ofStarAlgHom ρ₀) x).le_opNorm
        (rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ)
      rw [← hcn] at h
      exact h
    rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, n1, n1im, n2]
    nlinarith [norm_nonneg (rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ),
      norm_nonneg (spatialHom π (StarRep.ofStarAlgHom ρ₀) x
        (rightCoeffVector (StarRep.ofStarAlgHom ρ₀) ζ b ξ)), hb, hc0]
  have hadjr : IsAdjoint ((StarRep.ofStarAlgHom ρ₀).hom r)
      ((StarRep.ofStarAlgHom ρ₀).hom r) := by
    have h := (StarRep.ofStarAlgHom ρ₀).isAdjoint_star r
    rwa [hstar] at h
  have hop := norm_smul_one_sub_le_of_isAdjoint hadjr hρr
  have hiso : ∀ u : B, ‖ρ₀ u‖ = ‖u‖ := fun u =>
    NonUnitalStarAlgHom.norm_map ρ₀ hρ₀ u
  have hrB : ‖((‖r‖ : ℂ) • (1 : B)) - r‖ ≤ ‖r‖ := by
    have e2 : ρ₀ (((‖r‖ : ℂ) • (1 : B)) - r)
        = ((‖r‖ : ℂ) • (1 : K →L[ℂ] K)) - ρ₀ r := by
      rw [map_sub, map_smul, map_one]
    have e3 : ‖((‖r‖ : ℂ) • (1 : B)) - r‖
        = ‖((‖r‖ : ℂ) • (1 : K →L[ℂ] K)) - ρ₀ r‖ := by
      rw [← e2, hiso]
    have e4 : ‖ρ₀ r‖ = ‖r‖ := hiso r
    rw [e3, ← e4]
    exact hop
  have hstate : 0 ≤ (ψ.toCLM r).re :=
    re_apply_nonneg_of_norm_smul_one_sub_le ψ.toCLM ψ.map_one ψ.norm_le hrB
  have g1 : ⟪rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ,
      spatialHom π ψ.gnsRep (star x * x)
        (rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ)⟫_ℂ = ψ.toCLM z₂ := by
    rw [inner_rightCoeffVector_spatialHom π ψ.gnsRep b ξ ψ.gnsVector
      (star x * x), ← hz₂]
    exact inner_gnsVector_gnsRep ψ z₂
  have g2 : ⟪rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ,
      rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ⟫_ℂ = ψ.toCLM z₁ := by
    rw [inner_rightCoeffVector_self π ψ.gnsRep b ξ ψ.gnsVector, ← hz₁]
    exact inner_gnsVector_gnsRep ψ z₁
  have g3 : ‖spatialHom π ψ.gnsRep x
      (rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ)‖ ^ 2
      = (ψ.toCLM z₂).re := by
    rw [← re_inner_self, ← inner_spatialHom_star_mul_self, g1]
  have g4 : ‖rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ‖ ^ 2
      = (ψ.toCLM z₁).re := by
    rw [← re_inner_self, g2]
  have g5 : (ψ.toCLM r).re
      = c ^ 2 * (ψ.toCLM z₁).re - (ψ.toCLM z₂).re := by
    rw [hr_def, map_sub, map_smul, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have g6 : ‖spatialHom π ψ.gnsRep x
      (rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ)‖ ^ 2
      ≤ c ^ 2 * ‖rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ‖ ^ 2 := by
    rw [g3, g4]
    linarith [hstate, g5.le, g5.symm.le]
  have hnn : 0 ≤ ‖spatialHom π ψ.gnsRep x
      (rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ)‖ := norm_nonneg _
  have hnn2 : 0 ≤ c * ‖rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ‖ :=
    mul_nonneg hc0 (norm_nonneg _)
  refine (sq_le_sq₀ hnn hnn2).mp ?_
  have hsq : (c * ‖rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ‖) ^ 2
      = c ^ 2 * ‖rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ‖ ^ 2 := by ring
  rw [hsq]
  exact g6

end LegRight

/-! ## The hard half of Takesaki's identification -/

section MinLe

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- **The hard half of Takesaki's identification**: the canonical minimal
tensor norm is dominated by the spatial norm of any faithful pair of unital
⋆-representations on complete Hilbert spaces.  Each GNS leg of the defining
supremum is dominated one factor at a time, with the positivity transfer of
the coefficient calculus standing in for weak-⋆ density of vector states. -/
theorem minTensorNorm_le_spatialNorm (π₀ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ₀ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (hπ₀ : Function.Injective π₀)
    (hρ₀ : Function.Injective ρ₀) (x : A ⊗[ℂ] B) :
    minTensorNorm x
      ≤ spatialNorm (StarRep.ofStarAlgHom π₀) (StarRep.ofStarAlgHom ρ₀) x := by
  rw [minTensorNorm_apply]
  refine ciSup_le fun p => ?_
  calc spatialNorm p.1.gnsRep p.2.gnsRep x
      ≤ spatialNorm (StarRep.ofStarAlgHom π₀) p.2.gnsRep x :=
        spatialNorm_gnsRep_le_left π₀ hπ₀ p.1 p.2.gnsRep x
    _ ≤ spatialNorm (StarRep.ofStarAlgHom π₀) (StarRep.ofStarAlgHom ρ₀) x :=
        spatialNorm_gnsRep_le_right ρ₀ hρ₀ p.2 (StarRep.ofStarAlgHom π₀) x

end MinLe

end CStarTensor
end GroupApproximation
