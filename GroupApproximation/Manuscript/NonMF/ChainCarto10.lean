import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetInducedCoreSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: `J = p_C I p_C` at the printed generality

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`, tex 1749–1750:

> The return transient ideal is therefore $J=p_CIp_C$.                                (tex 1749–1750)

Setting, as printed for the corollary: `X` a compact metrizable totally disconnected nonempty space
(carried as a compact metric space), `T : X ≃ₜ X`, `C` a return section (`IsReturnSection T r C`),
`k` a finite field, `S_C = firstReturnHomeomorph hC`, `P_C = ReturnCorner k hC = p_C R_X p_C`,
`I = coreTransientIdeal T k` and `J = coreTransientIdeal S_C k`.

This module supersedes `Manuscript.NonMF.RankBudget.manuscriptSentence_returnTransientIdealEqCornerOfI`
(`RankBudget/InducedCore.lean:123`), whose statement carries an extra instance argument
`[CompactSpace C]` that the tex does not print.  That hypothesis is automatic: a return section is
clopen (`IsReturnSection.isClopen`), hence closed in the compact space `X`, hence compact
(`IsClosed.isCompact`), so `C` is a compact space (`isCompact_iff_compactSpace`).  This is
`compactSpace_of_isReturnSection`.

The transient ideal `J = coreTransientIdeal S_C k` needs a `CompactSpace C` instance to be written
down at all (`coreTransientIdeal` is stated over compact metric spaces), so the endpoint's type
supplies it with `haveI := compactSpace_of_isReturnSection hC`, which inlines the proof term: no
hypothesis is taken.  `CompactSpace` is a `Prop`, so this instance is definitionally the one used by
`DynamicRankBudget.printedReturnTransientIdeal_closed` and the proof is that closed theorem.
-/

namespace GroupApproximation.Manuscript.NonMF.ChainCarto10

/-- A return section of a homeomorphism of a compact space is a compact space: it is clopen, hence
closed, hence compact. -/
theorem compactSpace_of_isReturnSection {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X ≃ₜ X} {r : ℕ} {C : Set X} (hC : GroupApproximation.ChainCore.IsReturnSection T r C) :
    CompactSpace C :=
  isCompact_iff_compactSpace.mp hC.isClopen.isClosed.isCompact

#audit_axioms compactSpace_of_isReturnSection

/-- **tex 1749–1750**, "The return transient ideal is therefore $J=p_CIp_C$", with only the printed
hypotheses: under the return ring isomorphism `R_{S_C} ≃+* P_C = p_C R_X p_C`, an element `c` of the
return ring lies in the transient ideal `J` of `(C, S_C)` exactly when its image is `p_C a p_C` for
some `a ∈ I`.  Same statement as
`Manuscript.NonMF.RankBudget.manuscriptSentence_returnTransientIdealEqCornerOfI` without the
`[CompactSpace C]` argument (the compactness of `C` is proved, `compactSpace_of_isReturnSection`). -/
theorem manuscriptSentence_returnTransientIdealEqCornerOfI'
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : GroupApproximation.ChainCore.IsReturnSection T r C)
    (k : Type) [Field k] [Finite k]
    (c : GroupApproximation.ClopenCrossedProduct (GroupApproximation.ChainCore.firstReturnHomeomorph hC) k) :
    haveI : CompactSpace C := compactSpace_of_isReturnSection hC
    (∃ a ∈ GroupApproximation.ClopenCrossedProduct.coreTransientIdeal T k,
        ((GroupApproximation.ChainCore.returnRingEquiv k hC c :
            GroupApproximation.ChainCore.ReturnCorner k hC) : GroupApproximation.ClopenCrossedProduct T k) =
          GroupApproximation.ChainCore.returnP k hC * a * GroupApproximation.ChainCore.returnP k hC) ↔
      c ∈ GroupApproximation.ClopenCrossedProduct.coreTransientIdeal
        (GroupApproximation.ChainCore.firstReturnHomeomorph hC) k := by
  haveI : CompactSpace C := compactSpace_of_isReturnSection hC
  exact GroupApproximation.ChainCore.DynamicRankBudget.printedReturnTransientIdeal_closed X T r C hC k c

#audit_axioms manuscriptSentence_returnTransientIdealEqCornerOfI'

end GroupApproximation.Manuscript.NonMF.ChainCarto10
