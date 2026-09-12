import GroupApproximation.Analysis.LanceCPContractiveUnitalization
import GroupApproximation.Analysis.LanceNuclearity
import GroupApproximation.Analysis.CStarCPStarTarget
import GroupApproximation.Analysis.ReducedGroupCStarSpan
import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Analysis.BlackadarKirchbergStarEquivTransport
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Meta.AxiomGuard

/-!
# From finite-local NF approximations to the Lance UCP property

`IsNFAlgebra` supplies completely positive contractions through matrix
algebras.  `NuclearReducedCPAP` asks instead for unital completely positive
maps through the corresponding finite-dimensional operator algebra.  The
additive repair of `LanceCPContractiveUnitalization` closes the first gap with
an explicit factor-four loss; the canonical matrix/operator star-equivalence
closes the second.

The approximately multiplicative clause of an NF approximation is not needed
for this implication.  It is the input which Blackadar--Kirchberg construct
from nuclearity and an MF embedding in the converse half of their NF
characterization; once such NF data exist, the passage to the Lance CPAP is
unconditional.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace Matrix.Norms.L2Operator
open ReducedGroupCStarTrace

universe u

noncomputable section

local instance matrixBlockCStarAlgebra
    (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- Reindex a finite matrix block by its canonical enumeration and view it as
the bounded operators on the corresponding Euclidean space. -/
def finiteModelOperatorStarAlgEquiv (Y : FiniteModel) :
    Matrix Y Y ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card Y))) :=
  (matrixReindexStarAlgEquiv (Fintype.equivFin Y)).trans
    (Matrix.toEuclideanCLM (n := Fin (Fintype.card Y)) (𝕜 := ℂ))

/-- **Finite-local NF implies the translation-tested Lance CPAP.**

For each finite set of translations, include the unit in the NF test set and
ask for tolerance `epsilon / 4`.  Additively repairing both CPC legs makes them
unital and the quantitative repair theorem recovers the requested `epsilon`
bound.  Transport through `finiteModelOperatorStarAlgEquiv` is exact and
preserves complete positivity. -/
theorem nuclearReducedCPAP_of_isNFAlgebra
    (G : Type) [Group G]
    (hNF : IsNFAlgebra (ReducedGroupCStar G)) : NuclearReducedCPAP G := by
  classical
  intro F epsilon hepsilon
  let translation : G → ReducedGroupCStar G := fun g ↦
    ⟨leftRegularOperator G g, mem_reduced_leftRegularOperator g⟩
  let S : Finset (ReducedGroupCStar G) :=
    insert 1 (F.image translation)
  have hquarter : 0 < epsilon / 4 := div_pos hepsilon (by norm_num)
  obtain ⟨Y, hY, down, up, hdownCP, hupCP, hdownContract,
      hupContract, hrecover, -⟩ := hNF.localApproximation S (epsilon / 4) hquarter
  letI : Nonempty Y := hY
  let omegaA : CStarState.State (ReducedGroupCStar G) :=
    (CStarState.State.exists_star_mul_self (1 : ReducedGroupCStar G)).choose
  let omegaY : CStarState.State (Matrix Y Y ℂ) :=
    (CStarState.State.exists_star_mul_self (1 : Matrix Y Y ℂ)).choose
  let downU := additiveUnitalization down omegaA
  let upU := additiveUnitalization up omegaY
  have hdownU : IsCompletelyPositive downU ∧ downU 1 = 1 :=
    additiveUnitalization_completelyPositive_unital
      down omegaA hdownCP hdownContract
  have hupU : IsCompletelyPositive upU ∧ upU 1 = 1 :=
    additiveUnitalization_completelyPositive_unital
      up omegaY hupCP hupContract
  have hrecoverOne : ‖up (down 1) - 1‖ ≤ epsilon / 4 :=
    hrecover 1 (Finset.mem_insert_self 1 _)
  let e := finiteModelOperatorStarAlgEquiv Y
  let downOp :=
    (BlackadarKirchberg.starAlgEquivLinearMap e).comp downU
  let upReduced :=
    upU.comp (BlackadarKirchberg.starAlgEquivLinearMap e.symm)
  let inclStar :=
    (reducedGroupCStarSubalgebra G).subtype.toNonUnitalStarAlgHom
  let incl : ↥(reducedGroupCStarSubalgebra G) →ₗ[ℂ]
      (GroupHilbert G →L[ℂ] GroupHilbert G) := inclStar
  let upOp := incl.comp upReduced
  have heCP : IsCompletelyPositive
      (BlackadarKirchberg.starAlgEquivLinearMap e) :=
    isCompletelyPositive_of_starAlgHom
      e.toStarAlgHom.toNonUnitalStarAlgHom
  have heSymmCP : IsCompletelyPositive
      (BlackadarKirchberg.starAlgEquivLinearMap e.symm) :=
    isCompletelyPositive_of_starAlgHom
      e.symm.toStarAlgHom.toNonUnitalStarAlgHom
  have hinclCP : IsCompletelyPositive incl := by
    dsimp only [incl]
    exact isCompletelyPositive_of_starAlgHom inclStar
  have hdownOpCP : IsCompletelyPositive downOp := heCP.comp hdownU.1
  have hupReducedCP : IsCompletelyPositive upReduced := hupU.1.comp heSymmCP
  have hupOpCP : IsCompletelyPositive upOp := hinclCP.comp hupReducedCP
  refine ⟨Fintype.card Y, downOp, upOp, ?_, ?_, ?_, hupOpCP, ?_, ?_, ?_⟩
  · intro m a v
    by_cases hm : m = 0
    · subst m
      simp
    · letI : NeZero m := ⟨hm⟩
      exact (hdownOpCP.form_nonneg a v).1
  · intro a
    exact OrderZero.map_star_of_cp hdownOpCP a
  · dsimp only [downOp, LinearMap.comp_apply]
    rw [hdownU.2]
    exact map_one e
  · dsimp only [upOp, upReduced, incl, LinearMap.comp_apply]
    rw [BlackadarKirchberg.starAlgEquivLinearMap_apply, map_one e.symm, hupU.2]
    rfl
  · intro T
    dsimp only [upOp, incl, LinearMap.comp_apply]
    exact (upReduced T).property
  · intro g hg
    have htranslationMem : translation g ∈ S := by
      exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    have hrepair :
        ‖upU (downU (translation g)) - translation g‖ ≤ epsilon := by
      have h := norm_additiveUnitalization_comp_sub_le_four_mul
        down up omegaA omegaY hdownCP hupCP hdownContract hupContract
        hrecoverOne (translation g)
        (by
          change ‖leftRegularOperator G g‖ ≤ 1
          exact norm_leftRegularOperator_le_one G g)
        (hrecover _ htranslationMem)
      change ‖upU (downU (translation g)) - translation g‖ ≤ epsilon
      have hfour : 4 * (epsilon / 4) = epsilon := by ring
      rw [← hfour]
      exact h
    change ‖upOp (downOp (translation g)) - leftRegularOperator G g‖ ≤ epsilon
    have hval : upOp (downOp (translation g)) =
        (upU (downU (translation g)) : ReducedGroupCStar G) := by
      simp only [upOp, upReduced, downOp, incl, LinearMap.comp_apply,
        BlackadarKirchberg.starAlgEquivLinearMap_apply,
        StarAlgEquiv.symm_apply_apply]
      rfl
    rw [hval]
    exact hrepair

end

end CStarExactness
end GroupApproximation

open GroupApproximation.CStarExactness

#audit_axioms finiteModelOperatorStarAlgEquiv
#audit_axioms nuclearReducedCPAP_of_isNFAlgebra
