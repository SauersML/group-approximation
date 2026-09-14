import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetInducedCoreSaturation
import GroupApproximation.Manuscript.NonMFSentences.ChainCoreClosures
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the induced core is `C ∩ Y`, closed

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1743–1750:

> The induced core is $C\cap Y$.  Indeed its return ring is a corner
> of the LEF ring $R_Y$, so it lies in the induced chain-recurrent core.
> Conversely, saturating that core through the finite towers gives a
> closed invariant subsystem whose ring is a corner of a matrix ring
> over an LEF ring, hence LEF.  Theorem~\ref{thm:core-ring-reflection}
> applied to this subsystem makes every one of its points chain recurrent
> in $X$, proving the reverse inclusion.

`printedInducedCore_closed` closes ms-core-1's `image_chainRecurrentSet_firstReturn_printed`, whose two
inclusions follow the printed route (`mem_chainRecurrentSet_firstReturn_of_pieces`: the return ring of
`C ∩ Y` is a corner of the LEF ring `R_Y`, then Theorem `thm:core-ring-reflection`;
`coe_mem_chainRecurrentSet_of_firstReturn_of_pieces`: saturation through the towers, a corner of a
matrix ring over an LEF ring, then Theorem `thm:core-ring-reflection`).  Its two inputs are closed:
`coreRingReflectionStatement_holds` (`ChainCoreClosures`) and `coreModelsLEFStatement` (ms-core-2).
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

/-- **tex 1743, "The induced core is $C\cap Y$"**: for every return section `C` of `T`, the
chain-recurrent set of the first-return homeomorphism `S_C` is `C ∩ CR(T)`. -/
def PrintedInducedCore : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : IsReturnSection T r C),
    Subtype.val '' Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) =
      C ∩ Dynamics.chainRecurrentSet T

/-- **The induced core is `C ∩ Y`, closed** (tex 1743–1750), along the printed route. -/
theorem printedInducedCore_closed : PrintedInducedCore := by
  intro X _ _ _ _ T r C hC
  exact image_chainRecurrentSet_firstReturn_printed
    GroupApproximation.ChainCore.ChainCoreClosures.coreRingReflectionStatement_holds
    GroupApproximation.ChainCore.coreModelsLEFStatement T hC

end GroupApproximation.ChainCore.DynamicRankBudget

/-! ### Audit -/

#audit_closed_axioms GroupApproximation.ChainCore.DynamicRankBudget.printedInducedCore_closed
