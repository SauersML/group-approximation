import GroupApproximation.Analysis.TensorHyperfiniteIIOneFactor
import GroupApproximation.Analysis.VonNeumannSpatialIsomorphism
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(G) ⊗̄ 𝓡` is a McDuff factor

Lane `oa-mcduff` for `simple_kazhdan_sofic_group.tex` at origin/main 37551fd93, "Brown's formulation",
tex 280–283 (census row `97438886a277`): "`L(G) ⊗̄ 𝓡` is a McDuff factor [McDuff]".

`McDuff.IsMcDuffFactor M` asks for a II₁ factor with `M ≅ M ⊗̄ 𝓡`.  For `M = L(G) ⊗̄ 𝓡` the II₁ property
is `TwistedProduct.isIIOneFactor_tensorHyperfinite`, and the isomorphism is a chain of spatial
isomorphisms: with `Γ` the Pauli group and `β` its cocycle,

  `M ≅ L_{β⊕0}(Γ × G)`, `M ⊗̄ 𝓡 ≅ L_{β⊕0}(Γ × G) ⊗̄ 𝓡 ≅ L_{β⊕(β⊕0)}(Γ × (Γ × G)) ≅ L_{β⊕0}(Γ × G)`,

the last one by reindexing along `(γ₁, (γ₂, g)) ↦ (interleave (γ₁, γ₂), g)`, which carries the cocycle
by `Hyperfinite.pauliCocycle_interleave`.
-/

namespace GroupApproximation
namespace McDuff

open ReducedGroupCStarTrace TwistedGroupVonNeumann TwistedTensor TwistedProduct SpatialIso

noncomputable section

universe u

variable (G : Type u) [Group G]

/-- The reindexing `(γ₁, (γ₂, g)) ↦ (interleave (γ₁, γ₂), g)`. -/
def interleaveProd : Hyperfinite.PauliGroup × (Hyperfinite.PauliGroup × G) ≃* Hyperfinite.PauliGroup × G :=
  (MulEquiv.prodAssoc (M := Hyperfinite.PauliGroup) (N := Hyperfinite.PauliGroup) (P := G)).symm.trans
    (MulEquiv.prodCongr Hyperfinite.pauliInterleave (MulEquiv.refl G))

theorem interleaveProd_apply (x : Hyperfinite.PauliGroup × (Hyperfinite.PauliGroup × G)) :
    interleaveProd G x = (Hyperfinite.pauliInterleave (x.1, x.2.1), x.2.2) :=
  rfl

theorem prodCocycle_interleaveProd (x y : Hyperfinite.PauliGroup × (Hyperfinite.PauliGroup × G)) :
    prodCocycle Hyperfinite.pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2)) (interleaveProd G x)
        (interleaveProd G y) =
      prodCocycle Hyperfinite.pauliCocycle
        (prodCocycle Hyperfinite.pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2))) x y := by
  simp only [prodCocycle, interleaveProd_apply, Hyperfinite.pauliCocycle_interleave, add_zero]

/-- **`L(G) ⊗̄ 𝓡 ≅ (L(G) ⊗̄ 𝓡) ⊗̄ 𝓡`**, spatially. -/
def tensorHyperfiniteAbsorbs :
    ↥(twistedTensor (twistedVonNeumannAlgebra (fun _ _ : G ↦ (0 : ZMod 2)))
        Hyperfinite.pauliCocycle).toStarSubalgebra ≃⋆ₐ[ℂ]
      ↥(twistedTensor (twistedTensor (twistedVonNeumannAlgebra (fun _ _ : G ↦ (0 : ZMod 2)))
        Hyperfinite.pauliCocycle) Hyperfinite.pauliCocycle).toStarSubalgebra := by
  have h1 := curryConj_image_twistedTensor Hyperfinite.pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2))
    Hyperfinite.pauliCocycle_isSignCocycle (isSignCocycle_zero G)
  have h2 := conj_image_twistedTensor (Γ := Hyperfinite.PauliGroup) curryLp h1 Hyperfinite.pauliCocycle
  have h3 := curryConj_image_twistedTensor Hyperfinite.pauliCocycle
    (prodCocycle Hyperfinite.pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2)))
    Hyperfinite.pauliCocycle_isSignCocycle
    (isSignCocycle_prodCocycle Hyperfinite.pauliCocycle_isSignCocycle (isSignCocycle_zero G))
  have h4 := conj_image_twistedVonNeumannAlgebra_of_mulEquiv (interleaveProd G)
    (prodCocycle Hyperfinite.pauliCocycle
      (prodCocycle Hyperfinite.pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2))))
    (prodCocycle Hyperfinite.pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2)))
    (prodCocycle_interleaveProd G)
  exact ((restrictConj curryLp h1).trans (restrictConj _ h4).symm).trans
    ((restrictConj curryLp h3).symm.trans (restrictConj _ h2).symm)

/-- **`L(G) ⊗̄ 𝓡` is a McDuff factor** for an infinite ICC group `G`. -/
theorem isMcDuffFactor_tensorHyperfinite [Infinite G] (hG : TwoSidedRegularCommutant.IsICC G) :
    IsMcDuffFactor (tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra G)) := by
  refine ⟨isIIOneFactor_tensorHyperfinite G hG, ?_⟩
  show Nonempty (↥(twistedTensor (GroupVonNeumann.groupVonNeumannAlgebra G)
      Hyperfinite.pauliCocycle).toStarSubalgebra ≃⋆ₐ[ℂ]
    ↥(twistedTensor (twistedTensor (GroupVonNeumann.groupVonNeumannAlgebra G)
      Hyperfinite.pauliCocycle) Hyperfinite.pauliCocycle).toStarSubalgebra)
  rw [groupVonNeumannAlgebra_eq_twisted_zero G]
  exact ⟨tensorHyperfiniteAbsorbs G⟩

end

end McDuff
end GroupApproximation

#audit_axioms GroupApproximation.McDuff.isMcDuffFactor_tensorHyperfinite
