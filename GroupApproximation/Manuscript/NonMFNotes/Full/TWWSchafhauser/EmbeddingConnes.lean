import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesRoundingEndpoint
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesDensity
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesCPAP
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesSqrt
-- DRAFT (lane TWWSch3b1): replace the two leaf imports below by the files that hold
-- `isMatrixLeftBimoduleCPAP_of_isNuclearCStarAlgebra` (WO-3b1-A) and
-- `contractionSqrtCommutatorControl_holds` (WO-3b1-B) once they are on origin/main.
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesCPAPLeaf
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesSqrtLeaf

/-!
# Nuclear C⋆-algebras have amenable traces

Lane TWWSch3b1 (work order WO-TWWSch-3b-1).  Manuscript: `non_mf_group_notes.tex`, the
Tikuisis--White--Winter input "every faithful trace on a separable nuclear C⋆-algebra is
amenable".  Source: Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*,
Thm 6.2.7 and Prop 2.2.6.

The chain is:

1. nuclear ⇒ matrix left-bimodule CPAP (`isMatrixLeftBimoduleCPAP_of_isNuclearCStarAlgebra`)
   ⇒ matrix CPAP (`Connes.isMatrixCPAP_of_leftBimodule`);
2. Powers--Størmer for one contraction (`contractionSqrtCommutatorControl_holds`)
   ⇒ square-root control (`Connes.hasSqrtCommutatorControl_of_contraction`);
3. these give approximately invariant densities (`Connes.hasApproxInvariantDensities_of_gap`);
4. Connes' trick gives a locally amenable trace
   (`Connes.isLocallyAmenableTrace_of_hasApproxInvariantDensities`);
5. separability and a diagonal argument give an amenable trace
   (`isAmenableTrace_of_isLocallyAmenableTrace`).
-/

namespace GroupApproximation.Full.TWWSchafhauser

universe u

/-- **Tikuisis--White--Winter input** (Brown--Ozawa 6.2.7).  Every faithful tracial state
on a separable nuclear C⋆-algebra is amenable.  (Faithfulness is not used.) -/
theorem isAmenableTrace_of_isNuclearCStarAlgebra {A : Type u} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A]
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A) (τ : FaithfulTracialState A) :
    Quasidiagonal.IsAmenableTrace (fun a : A => τ a) :=
  Manuscript.NonMF.TWWLanes.NuclearAmenable.isAmenableTrace_of_isLocallyAmenableTrace
    ‹TopologicalSpace.SeparableSpace A› τ.toLinearMap τ.map_one
    (Connes.isLocallyAmenableTrace_of_hasApproxInvariantDensities
      (Connes.hasApproxInvariantDensities_of_gap
        (Connes.isMatrixCPAP_of_leftBimodule
          (isMatrixLeftBimoduleCPAP_of_isNuclearCStarAlgebra hnuc))
        (Connes.hasSqrtCommutatorControl_of_contraction contractionSqrtCommutatorControl_holds A)
        τ.toTracialState))

end GroupApproximation.Full.TWWSchafhauser
