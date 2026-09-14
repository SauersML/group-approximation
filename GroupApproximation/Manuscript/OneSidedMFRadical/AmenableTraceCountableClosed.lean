import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Sofic.NormApproximableDirectLimit
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:amenable-trace`: the non-MF witness is countable

`non_mf_groups_exist.tex`, Theorem `thm:amenable-trace`, first sentence (tex 263, census row `d4c878a7ac22`):

> There is a sofic group $W=W_0\rtimes\mathbb Z$, with $W_0$ locally residually finite, that is not MF.

MF is defined for countable groups (tex 87).  `AmenableTraceTheorem.PrintedAmenableNonquasidiagonalTrace` never
displays `Countable W`, and `¬ IsOperatorMF W` holds for every group larger than the continuum, so the display
alone does not certify "not MF" in the printed sense.  The concrete witness `WitnessGroup` is countable
(`MarkedCompression`'s instance, over the countable `ExplicitLinearModel.gammaBar`).  This module states the
theorem with `Countable W` displayed and proves it with nothing assumed, along the same route as
`manuscriptAmenableNonquasidiagonalTrace`.

* `PrintedAmenableNonquasidiagonalTraceCountable`, `printedAmenableNonquasidiagonalTraceCountable`.
-/

namespace GroupApproximation
namespace AmenableTraceTheorem

open LiteralNonMFLinearWitness CliffordWitnessLocallyRFByInt
open LocallyRFByIntAmenableTrace

/-- **Theorem `thm:amenable-trace`** (tex 263–270), with the countability of `W` displayed. -/
def PrintedAmenableNonquasidiagonalTraceCountable : Prop :=
  ∃ (W K : Type) (_ : Group W) (_ : Group K) (_ : Countable W)
    (φ : Multiplicative ℤ →* MulAut K),
    Nonempty (W ≃* (K ⋊[φ] Multiplicative ℤ)) ∧
      IsLocallyResiduallyFinite K ∧
      IsSofic W ∧
      ¬ IsOperatorMF W ∧
      Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar K ↦ canonicalMaximalTrace K a) ∧
      Quasidiagonal.IsAmenableTrace
        (fun a : MaximalGroupCStar W ↦ canonicalMaximalTrace W a) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar W ↦ canonicalMaximalTrace W a)

theorem printedAmenableNonquasidiagonalTraceCountable :
    PrintedAmenableNonquasidiagonalTraceCountable := by
  obtain ⟨hEquiv, hKlocRF, hSofic, hNotMF, hKQD, hAmen, hNotQD⟩ :=
    manuscriptAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal
      AmenableExtensionTrace.manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal
  exact ⟨WitnessGroup, ShiftKernel, inferInstance, inferInstance, inferInstance, shiftAction,
    hEquiv, hKlocRF, hSofic, hNotMF, hKQD, hAmen, hNotQD⟩

/-- **"Since $W_0$ is a direct limit of residually finite groups, it is MF"** (tex 284–286), along the printed
route: a countable group exhausted by residually finite subgroups is MF (Korchagin, Corollary 10 and
Proposition 13), and `W_0` is such a group, its finitely generated subgroups being residually finite. -/
def PrintedShiftKernelDirectLimitMF : Prop :=
  (∀ (G : Type) [Group G] [Countable G],
    (∀ F : Finset G, ∃ H : Subgroup G, (∀ g ∈ F, g ∈ H) ∧ Group.ResiduallyFinite H) → IsOperatorMF G) ∧
    IsOperatorMF ShiftKernel

theorem printedShiftKernelDirectLimitMF : PrintedShiftKernelDirectLimitMF := by
  refine ⟨fun G _ _ h => (isWeakMF_of_forall_finset_residuallyFinite_subgroup h).isOperatorMF, ?_⟩
  refine (isWeakMF_of_forall_finset_residuallyFinite_subgroup fun F => ?_).isOperatorMF
  exact ⟨Subgroup.closure (F : Set ShiftKernel), fun g hg => Subgroup.subset_closure hg,
    shiftKernel_isLocallyResiduallyFinite _ ⟨F, rfl⟩⟩

end AmenableTraceTheorem
end GroupApproximation

#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.printedAmenableNonquasidiagonalTraceCountable
#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.printedShiftKernelDirectLimitMF
