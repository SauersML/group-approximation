import GroupApproximation.Manuscript.NonMFSentences.ChainCoreModelsStatement
import GroupApproximation.Dynamics.InvolutionLocalizationRingClosed
import GroupApproximation.Dynamics.TransientSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:chain-core-models`, every printed sentence

> The set `Y` is nonempty, closed and invariant, and `R_Y` is LEF.
> The complement `X \ Y` is covered by translates of sets `P \ T(P)`, where `P` is clopen and
> `T(P) ⊆ P`.  Each of these sets is wandering: its distinct integer translates are pairwise
> disjoint.

The three sentences are already proved on the tree, separately:

* `ChainCore.printedChainCoreModelsFirstSentence` (nonempty, closed, invariant, LEF);
* `ClopenCrossedProduct.chainCoreDefectCoverStatement_holds` (the defect cover);
* `ClopenCrossedProduct.isWandering_defect` (each defect `P \ T(P)` is wandering).

This file only packages them into one zero-input declaration for the margin badge.
-/

namespace GroupApproximation.Full.NM12

/-- **`lem:chain-core-models`** as printed: the first sentence, the defect cover of the
complement of the chain-recurrent set, and the wandering property of every defect `P \ T(P)`
of a clopen `P` with `T(P) ⊆ P`. -/
def PrintedChainCoreModels : Prop :=
  GroupApproximation.ChainCore.PrintedChainCoreModelsFirstSentence ∧
    GroupApproximation.ClopenCrossedProduct.ChainCoreDefectCoverStatement ∧
      ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
        (T : X ≃ₜ X) (P : Set X), IsClopen P → T '' P ⊆ P →
          GroupApproximation.Dynamics.IsWandering T.toEquiv (P \ T '' P)

/-- **`lem:chain-core-models`, closed.** -/
theorem printedChainCoreModels_closed : PrintedChainCoreModels := by
  refine ⟨GroupApproximation.ChainCore.printedChainCoreModelsFirstSentence,
    GroupApproximation.ClopenCrossedProduct.chainCoreDefectCoverStatement_holds, ?_⟩
  intro _ _ _ _ _ T _ _ hP
  exact GroupApproximation.ClopenCrossedProduct.isWandering_defect (T := T) hP

end GroupApproximation.Full.NM12

#audit_closed_axioms GroupApproximation.Full.NM12.printedChainCoreModels_closed
