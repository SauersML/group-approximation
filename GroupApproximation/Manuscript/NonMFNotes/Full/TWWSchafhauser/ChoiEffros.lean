import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosClosure
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosFiniteDim
import GroupApproximation.Analysis.LanceCPContractiveUnitalization

/-!
# The Choi–Effros lifting theorem

Lane `TWWSchafhauser-3a` (work order `WO-TWWCore-3`, piece 3a).

Let `A` be a separable nuclear C⋆-algebra and `π : B → C` a surjective
`⋆`-homomorphism of C⋆-algebras (so `C ≅ B / ker π`).  Then

* every completely positive contraction `φ : A → C` lifts to a completely
  positive contraction `ψ : A → B` (`exists_cpc_lift_of_isNuclear`);
* for nontrivial `A`, every unital completely positive `φ : A → C` lifts to a
  unital completely positive `ψ : A → B` (`exists_ucp_lift_of_isNuclear`).

Route: a nuclear cpc map factors approximately through matrix algebras, whose
cpc maps lift exactly (`exists_cpc_approx_lift_of_isNuclearMap`), and Arveson's
closure theorem turns approximate cpc lifts into an exact one
(`exists_cpc_lift_of_approx`).  The unital case adds the unit defect weighted by
a state (`CStarExactness.additiveUnitalization`).

Sources: M.-D. Choi, E. G. Effros, *The completely positive lifting problem for
C⋆-algebras*, Ann. of Math. (2) **104** (1976), 585–609, Theorem 3.10;
W. Arveson, *Notes on extensions of C⋆-algebras*, Duke Math. J. **44** (1977),
329–355, §2; N. P. Brown, N. Ozawa, *C⋆-algebras and finite-dimensional
approximations*, Theorem C.3.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

universe u v w

/-- **Choi–Effros lifting for nuclear maps.**  A nuclear contraction on a
separable C⋆-algebra into a quotient has a completely positive contractive lift.
(Complete positivity of `φ` is part of the published interface but is not needed:
nuclear maps are limits of completely positive maps.) -/
theorem exists_cpc_lift_of_isNuclearMap {A : Type u} {B : Type v} {C : Type w}
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] [CStarAlgebra B] [CStarAlgebra C]
    (π : B →⋆ₐ[ℂ] C) (hπ : Function.Surjective π) (φ : A →ₗ[ℂ] C)
    (hnuc : CStarExactness.IsNuclearMap φ) (_hφ : CStarExactness.IsCompletelyPositive φ)
    (hφc : ∀ a, ‖φ a‖ ≤ ‖a‖) :
    ∃ ψ : A →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive ψ ∧ (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧
      ∀ a, π (ψ a) = φ a :=
  exists_cpc_lift_of_approx π hφc (exists_cpc_approx_lift_of_isNuclearMap π hπ hnuc)

/-- A completely positive contraction out of a nuclear C⋆-algebra is a nuclear
map: compose the approximate factorization of the identity with `φ`. -/
theorem isNuclearMap_of_isNuclearCStarAlgebra {A : Type u} {C : Type w}
    [CStarAlgebra A] [CStarAlgebra C] (hA : CStarExactness.IsNuclearCStarAlgebra A)
    {φ : A →ₗ[ℂ] C} (hφ : CStarExactness.IsCompletelyPositive φ)
    (hφc : ∀ a, ‖φ a‖ ≤ ‖a‖) :
    CStarExactness.IsNuclearMap φ := by
  intro F ε hε
  obtain ⟨D, α, β, hα, hβ, hαc, hβc, happ⟩ := hA F ε hε
  refine ⟨D, α, φ ∘ₗ β, hα, hφ.comp hβ, hαc, fun d ↦ (hφc _).trans (hβc d), fun a ha ↦ ?_⟩
  rw [LinearMap.comp_apply, ← map_sub]
  exact (hφc _).trans (happ a ha)

/-- **The Choi–Effros lifting theorem (contractive form).**  Every completely
positive contraction from a separable nuclear C⋆-algebra into a quotient has a
completely positive contractive lift. -/
theorem exists_cpc_lift_of_isNuclear {A : Type u} {B : Type v} {C : Type w}
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] [CStarAlgebra B] [CStarAlgebra C]
    (hA : CStarExactness.IsNuclearCStarAlgebra A)
    (π : B →⋆ₐ[ℂ] C) (hπ : Function.Surjective π) (φ : A →ₗ[ℂ] C)
    (hφ : CStarExactness.IsCompletelyPositive φ) (hφc : ∀ a, ‖φ a‖ ≤ ‖a‖) :
    ∃ ψ : A →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive ψ ∧ (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧
      ∀ a, π (ψ a) = φ a :=
  exists_cpc_lift_of_isNuclearMap π hπ φ (isNuclearMap_of_isNuclearCStarAlgebra hA hφ hφc)
    hφ hφc

/-- **The Choi–Effros lifting theorem (unital form).**  Every unital completely
positive map from a nontrivial separable nuclear C⋆-algebra into a quotient has
a unital completely positive lift. -/
theorem exists_ucp_lift_of_isNuclear {A : Type u} {B : Type v} {C : Type w}
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] [Nontrivial A]
    [CStarAlgebra B] [CStarAlgebra C]
    (hA : CStarExactness.IsNuclearCStarAlgebra A)
    (π : B →⋆ₐ[ℂ] C) (hπ : Function.Surjective π) (φ : A →ₗ[ℂ] C)
    (hφ : CStarExactness.IsCompletelyPositive φ) (hφ1 : φ 1 = 1) :
    ∃ ψ : A →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive ψ ∧ ψ 1 = 1 ∧
      ∀ a, π (ψ a) = φ a := by
  have hφc : ∀ a, ‖φ a‖ ≤ ‖a‖ :=
    norm_apply_le_of_norm_map_one_le hφ (by
      rw [hφ1]
      exact choiEffros_norm_one_le)
  obtain ⟨ψ, hψ, hψc, hψπ⟩ := exists_cpc_lift_of_isNuclear hA π hπ φ hφ hφc
  obtain ⟨ω, -⟩ := CStarState.exists_state_norm_le_gnsRep (1 : A)
  obtain ⟨hcp, hone⟩ :=
    CStarExactness.additiveUnitalization_completelyPositive_unital ψ ω hψ hψc
  refine ⟨CStarExactness.additiveUnitalization ψ ω, hcp, hone, fun a ↦ ?_⟩
  rw [CStarExactness.additiveUnitalization_apply, map_add, map_smul, map_sub, map_one,
    hψπ, hψπ, hφ1, sub_self, smul_zero, add_zero]

end

end TWWSchafhauser
end Full
end GroupApproximation
