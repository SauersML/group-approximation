import GroupApproximation.Analysis.TwistedTensorProductAlgebra
import GroupApproximation.Analysis.McDuffFactor
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(G) ⊗̄ 𝓡` is a II₁ factor

Lane `oa-mcduff` for `simple_kazhdan_sofic_group.tex` at origin/main 37551fd93, "Brown's formulation",
tex 280–283 (census row `97438886a277`): "`L(G) ⊗̄ 𝓡` is a McDuff factor".  A McDuff factor is in
particular a II₁ factor; this module proves that half.

* `isIIOneFactor_of_conj_image`: II₁ factors pull back along a spatial isomorphism `Ad U`.
* `isIIOneFactor_tensorHyperfinite`: for an infinite ICC group `G`, `L(G) ⊗̄ 𝓡` is a II₁ factor.  By
  `groupVonNeumannAlgebra_eq_twisted_zero` and `curryConj_image_twistedTensor`, `Ad U` carries
  `L(G) ⊗̄ 𝓡` onto the twisted group von Neumann algebra of `Γ × G` for the sum of the Pauli cocycle
  and `0`, which is twisted ICC (`isTwistedICC_prodCocycle`), hence a II₁ factor by oa-hyperfinite's
  `isIIOneFactor_twistedVonNeumannAlgebra`.
-/

namespace GroupApproximation
namespace TwistedProduct

open ReducedGroupCStarTrace TwistedGroupVonNeumann TwistedTensor IIOneFactor
open scoped InnerProductSpace

noncomputable section

universe u v

section Transport

variable {H : Type u} {K : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **II₁ factors pull back along a spatial isomorphism.** -/
theorem isIIOneFactor_of_conj_image (U : H ≃ₗᵢ[ℂ] K) {M : VonNeumannAlgebra H}
    {N : VonNeumannAlgebra K}
    (hMN : U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)) = (N : Set (K →L[ℂ] K)))
    (hN : IsIIOneFactor N) : IsIIOneFactor M := by
  set Φ := U.conjStarAlgEquiv with hΦ
  have hmem : ∀ {T : H →L[ℂ] H}, T ∈ M → Φ T ∈ N := fun {T} hT ↦ by
    have h : Φ T ∈ (N : Set (K →L[ℂ] K)) := hMN ▸ ⟨T, hT, rfl⟩
    exact h
  have hmem' : ∀ {S : K →L[ℂ] K}, S ∈ N → Φ.symm S ∈ M := fun {S} hS ↦ by
    have h : S ∈ Φ '' (M : Set (H →L[ℂ] H)) := hMN.symm ▸ hS
    obtain ⟨T, hT, rfl⟩ := h
    rwa [Φ.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro T hTM hTc
    have hc : Φ T ∈ N.commutant := by
      rw [VonNeumannAlgebra.mem_commutant_iff]
      intro S hS
      have h := VonNeumannAlgebra.mem_commutant_iff.mp hTc (Φ.symm S) (hmem' hS)
      have h2 := congrArg Φ h
      rwa [map_mul, map_mul, Φ.apply_symm_apply] at h2
    obtain ⟨z, hz⟩ := hN.isFactor (Φ T) (hmem hTM) hc
    refine ⟨z, ?_⟩
    have h := congrArg Φ.symm hz
    rwa [Φ.symm_apply_apply, map_smul, map_one] at h
  · intro hfin
    apply hN.infinite_dimensional
    let e : ↥M.toStarSubalgebra ≃ₗ[ℂ] ↥N.toStarSubalgebra :=
      { toFun := fun T ↦ ⟨Φ T, hmem T.2⟩
        invFun := fun S ↦ ⟨Φ.symm S, hmem' S.2⟩
        map_add' := fun T S ↦ Subtype.ext (map_add Φ (T : H →L[ℂ] H) S)
        map_smul' := fun c T ↦ Subtype.ext (map_smul Φ c (T : H →L[ℂ] H))
        left_inv := fun T ↦ Subtype.ext (Φ.symm_apply_apply (T : H →L[ℂ] H))
        right_inv := fun S ↦ Subtype.ext (Φ.apply_symm_apply (S : K →L[ℂ] K)) }
    exact Module.Finite.equiv e
  · obtain ⟨τ, hτ⟩ := hN.exists_trace
    obtain ⟨ξ, η, hsum, hrep⟩ := hτ.normal
    refine ⟨fun T ↦ τ (Φ T),
      { normal := ⟨fun n ↦ U.symm (ξ n), fun n ↦ U.symm (η n), ?_, fun T hT ↦ ?_⟩
        map_one := ?_
        nonneg := fun T hT ↦ ?_
        tracial := fun T hT S hS ↦ ?_
        faithful := fun T hT h ↦ ?_ }⟩
    · simpa only [LinearIsometryEquiv.norm_map] using hsum
    · show τ (Φ T) = _
      rw [hrep (Φ T) (hmem hT)]
      refine tsum_congr fun n ↦ ?_
      change ⟪ξ n, U (T (U.symm (η n)))⟫_ℂ = ⟪U.symm (ξ n), T (U.symm (η n))⟫_ℂ
      calc ⟪ξ n, U (T (U.symm (η n)))⟫_ℂ
          = ⟪U (U.symm (ξ n)), U (T (U.symm (η n)))⟫_ℂ := by rw [U.apply_symm_apply]
        _ = ⟪U.symm (ξ n), T (U.symm (η n))⟫_ℂ := U.inner_map_map _ _
    · show τ (Φ 1) = 1
      rw [map_one]
      exact hτ.map_one
    · show 0 ≤ τ (Φ (star T * T))
      rw [map_mul, map_star]
      exact hτ.nonneg (Φ T) (hmem hT)
    · show τ (Φ (T * S)) = τ (Φ (S * T))
      rw [map_mul, map_mul]
      exact hτ.tracial (Φ T) (hmem hT) (Φ S) (hmem hS)
    · have h' : τ (star (Φ T) * Φ T) = 0 := by
        have h0 : τ (Φ (star T * T)) = 0 := h
        rwa [map_mul, map_star] at h0
      have hz := hτ.faithful (Φ T) (hmem hT) h'
      have h2 := congrArg Φ.symm hz
      rwa [Φ.symm_apply_apply, map_zero] at h2

end Transport

section Group

variable (G : Type u) [Group G]

/-- **`L(G) ⊗̄ 𝓡` is a II₁ factor** for an infinite ICC group `G`. -/
theorem isIIOneFactor_tensorHyperfinite [Infinite G] (hG : TwoSidedRegularCommutant.IsICC G) :
    IsIIOneFactor (McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra G)) := by
  show IsIIOneFactor (twistedTensor (GroupVonNeumann.groupVonNeumannAlgebra G) Hyperfinite.pauliCocycle)
  rw [groupVonNeumannAlgebra_eq_twisted_zero G]
  refine isIIOneFactor_of_conj_image curryLp
    (curryConj_image_twistedTensor Hyperfinite.pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2))
      Hyperfinite.pauliCocycle_isSignCocycle (isSignCocycle_zero G)) ?_
  exact isIIOneFactor_twistedVonNeumannAlgebra
    (prodCocycle Hyperfinite.pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2)))
    (isSignCocycle_prodCocycle Hyperfinite.pauliCocycle_isSignCocycle (isSignCocycle_zero G))
    (isTwistedICC_prodCocycle Hyperfinite.pauliCocycle_isSignCocycle (isSignCocycle_zero G)
      Hyperfinite.pauliCocycle_isTwistedICC (isTwistedICC_zero_of_isICC hG))

end Group

end

end TwistedProduct
end GroupApproximation

#audit_axioms GroupApproximation.TwistedProduct.isIIOneFactor_tensorHyperfinite
