import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.LocAmenTraceKraus
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.LocAmenTraceUcp
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.Glue
import GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.FormBridge
import GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.RoundingEndpoint
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosUcpReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-29, part 3: `ChoiEffrosUcpKrausStatement` for nuclear algebras, proved

Let `A` be nuclear.  Then `NuclearDensity.ChoiEffrosUcpKrausStatement A` holds
(`locAmenTrace_ucpKraus_of_isNuclear`).  This discharges the `hkraus` hypothesis of the
lane nm-tww-28c composite `NuclearDensity.choiEffrosUcp_nuclearTraceApproxDensityStatement`.

* If `A` is trivial, take the empty model.
* Otherwise take ucp maps `ρ₀ : A → M_Z` and `ψ₀ : M_Z → A` from
  `locAmenTrace_exists_ucpMatrixApproximation`, and a Kraus column `G` on the layered model
  with `ψ_G ∘ layer = ψ₀` from `locAmenTrace_exists_krausColumn`.
* Set `ρ = layer ∘ ρ₀`.  It is ucp in the form sense by `ConnesTrick.layerLinear_comp_ucp`,
  after `CoronaChoiEffros.isCompletelyPositiveOnMatrices_of_isCompletelyPositive`.
* The unit clause is `⟨G, G⟩ = ψ_G 1 = ψ_G (layer 1) = ψ₀ 1 = 1`.

## Truth check and remaining gap

The target `NuclearLocallyAmenableTraceStatement` is **TRUE**: every tracial state of a nuclear
C⋆-algebra is amenable (Brown--Ozawa 6.2.7).  With this file the target reduces to the single
Statement `NuclearDensity.ContractionSqrtCommutatorStatement`
(`locAmenTrace_nuclearLocallyAmenableTrace_of_contractionSqrt`).

**LOUD: that residual is TRUE (a Powers--Størmer type matrix inequality) and it is not strictly
weaker in logical strength, because every statement in the chain is true.**  It is strictly
smaller in proof content: a single finite-dimensional inequality, no Choi--Effros.  It is owned
by the PowersStormer sibling lane; see `LocAmenTraceOutright.lean` for the unconditional wiring.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearAmenable

open Quasidiagonal CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

attribute [local instance] CStarExactness.matrixBlockCStarAlgebraForLanceForward

/-- **Choi--Effros in Kraus form, proved.**  Every nuclear C⋆-algebra satisfies
`ChoiEffrosUcpKrausStatement`. -/
theorem locAmenTrace_ucpKraus_of_isNuclear {A : Type u} [CStarAlgebra A]
    (hnuc : IsNuclearCStarAlgebra A) : NuclearDensity.ChoiEffrosUcpKrausStatement A := by
  intro F δ hδ
  rcases subsingleton_or_nontrivial A with hA | hA
  · refine ⟨⟨Fin 0, inferInstance, inferInstance⟩, 0, fun _ ↦ 0, ?_, ?_,
      Subsingleton.elim _ _, ?_⟩
    · first
        | exact Matrix.ext fun i _ ↦ Fin.elim0 i
        | exact Subsingleton.elim _ _
    · first
        | exact isCompletelyPositiveOnMatrices_zero _
        | (rw [LinearMap.coe_zero]; exact isCompletelyPositiveOnMatrices_zero _)
    · intro a _
      exact (congrArg norm (Subsingleton.elim _ (0 : A))).trans_le (norm_zero.trans_le hδ.le)
  · obtain ⟨Z, hZ, ρ₀, ψ₀, hρCP, hρ1, hψCP, hψ1, happ⟩ :=
      locAmenTrace_exists_ucpMatrixApproximation hnuc F δ hδ
    letI : Nonempty Z := hZ
    obtain ⟨P, hP⟩ := locAmenTrace_exists_krausColumn Z ψ₀ hψCP
    have hform : IsCompletelyPositiveOnMatrices Z ⇑ρ₀ :=
      CoronaChoiEffros.isCompletelyPositiveOnMatrices_of_isCompletelyPositive Z ρ₀ hρCP
    obtain ⟨h1, hcp⟩ :=
      ConnesTrick.layerLinear_comp_ucp (fun _ ↦ Fintype.card Z) ρ₀ hρ1 hform
    refine ⟨ConnesTrick.layerModel Z (fun _ ↦ Fintype.card Z),
      ConnesTrick.layerLinear (fun _ ↦ Fintype.card Z) ∘ₗ ρ₀,
      locAmenTraceColumn Z (Fintype.card Z) P, h1, hcp, ?_, ?_⟩
    · exact (NuclearDensity.choiEffros_krausMap_one
          (locAmenTraceColumn Z (Fintype.card Z) P)).symm.trans
        ((congrArg (NuclearDensity.choiEffrosKrausMap (locAmenTraceColumn Z (Fintype.card Z) P))
          (ConnesTrick.layer_one (fun _ ↦ Fintype.card Z)).symm).trans ((hP 1).trans hψ1))
    · intro a ha
      exact (congrArg (fun x ↦ ‖x - a‖) (hP (ρ₀ a))).trans_le (happ a ha)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTrace_ucpKraus_of_isNuclear

/-- The nuclear trace density Statement, from the square-root commutator Statement alone. -/
theorem locAmenTrace_nuclearTraceApproxDensity_of_contractionSqrt
    (hsqrt : NuclearDensity.ContractionSqrtCommutatorStatement) :
    NuclearTraceApproxDensityStatement.{u} :=
  NuclearDensity.choiEffrosUcp_nuclearTraceApproxDensityStatement
    (fun A inst hn ↦ @locAmenTrace_ucpKraus_of_isNuclear A inst hn) hsqrt

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTrace_nuclearTraceApproxDensity_of_contractionSqrt

/-- **Lane nm-tww-29 reduction.**  `NuclearLocallyAmenableTraceStatement` follows from
`ContractionSqrtCommutatorStatement` alone. -/
theorem locAmenTrace_nuclearLocallyAmenableTrace_of_contractionSqrt
    (hsqrt : NuclearDensity.ContractionSqrtCommutatorStatement) :
    NuclearLocallyAmenableTraceStatement.{u} :=
  nuclearLocallyAmenableTrace_of_connesTrick_of_nuclearDensity
    ConnesTrick.connesTrickStatement_holds
    (locAmenTrace_nuclearTraceApproxDensity_of_contractionSqrt hsqrt)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTrace_nuclearLocallyAmenableTrace_of_contractionSqrt

end

end Manuscript.NonMF.TWWLanes.NuclearAmenable
end GroupApproximation
