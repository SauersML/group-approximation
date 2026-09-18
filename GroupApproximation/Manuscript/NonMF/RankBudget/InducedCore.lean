import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetInducedCoreSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the induced core and the return transient ideal

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`, tex 1743–1750:

> The induced core is $C\cap Y$.  Indeed its return ring is a corner
> of the LEF ring $R_Y$, so it lies in the induced chain-recurrent core.            (tex 1743–1745)
> Conversely, saturating that core through the finite towers gives a
> closed invariant subsystem whose ring is a corner of a matrix ring
> over an LEF ring, hence LEF.                                                        (tex 1745–1747)
> Theorem~\ref{thm:core-ring-reflection} applied to this subsystem makes every one of its points
> chain recurrent in $X$, proving the reverse inclusion.                              (tex 1747–1749)
> The return transient ideal is therefore $J=p_CIp_C$.                                (tex 1749–1750)

Setting, as printed for the corollary: `X` a compact metrizable totally disconnected nonempty space
(carried as a compact metric space), `T : X ≃ₜ X`, `C` a return section (`IsReturnSection T r C`),
`k` a finite field, `Y = CR(T)` (`Dynamics.chainRecurrentSet T`), `S_C = firstReturnHomeomorph hC`,
`R_Y = ClopenCrossedProduct (restrictHomeo T _) k`, `P_C = ReturnCorner k hC = p_C R_X p_C`,
`I = coreTransientIdeal T k` and `J = coreTransientIdeal S_C k`.

Proof route.  Each endpoint states the printed sentence with these concrete objects and every
hypothesis spelled out, and is the instance of the corresponding closed theorem of
`Manuscript/NonMFSentences/DynamicRankBudgetInducedCoreSentences`
(`printedInducedCoreCorner_closed`, `printedCoreSaturationLEF_closed`,
`printedCoreSaturationRecurrent_closed`, `printedReturnTransientIdeal_closed`).  Those are proved
along the printed route over the closed theorems `coreModelsLEFStatement` (`R_Y` is LEF),
`ChainCoreClosures.coreRingReflectionStatement_holds` (Theorem `thm:core-ring-reflection`), the
return-ring isomorphism `returnRingEquiv : R_{S_C} ≃+* P_C`, and the saturation lemmas of
`Dynamics/ReturnSaturation`; none of them takes a hypothesis standing for a cited result.
-/

namespace GroupApproximation.Manuscript.NonMF.RankBudget

/-- **tex 1743–1745**, "Indeed its return ring is a corner of the LEF ring $R_Y$, so it lies in the
induced chain-recurrent core": for every finite field `k`, the return ring of `C ∩ Y` for `T|_Y` is
isomorphic to the corner `P_{C∩Y}` of `R_Y`, `R_Y` is LEF and so is that return ring; and
`C ∩ Y ⊆ CR(S_C)`. -/
theorem manuscriptSentence_inducedCoreReturnRingCornerOfLEF
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : GroupApproximation.ChainCore.IsReturnSection T r C) :
    (∀ (k : Type) [Field k] [Finite k],
      Nonempty (GroupApproximation.ClopenCrossedProduct
          (GroupApproximation.ChainCore.firstReturnHomeomorph
            (GroupApproximation.ChainCore.DynamicRankBudget.isReturnSection_restrict hC
              (GroupApproximation.ChainCore.DynamicRankBudget.image_core T))) k ≃+*
          GroupApproximation.ChainCore.ReturnCorner k
            (GroupApproximation.ChainCore.DynamicRankBudget.isReturnSection_restrict hC
              (GroupApproximation.ChainCore.DynamicRankBudget.image_core T))) ∧
        GroupApproximation.Pestov91.IsLEFRing
          (GroupApproximation.ClopenCrossedProduct
            (GroupApproximation.ClopenCrossedProduct.restrictHomeo T
              (GroupApproximation.ChainCore.DynamicRankBudget.image_core T)) k) ∧
        GroupApproximation.Pestov91.IsLEFRing
          (GroupApproximation.ClopenCrossedProduct
            (GroupApproximation.ChainCore.firstReturnHomeomorph
              (GroupApproximation.ChainCore.DynamicRankBudget.isReturnSection_restrict hC
                (GroupApproximation.ChainCore.DynamicRankBudget.image_core T))) k)) ∧
      C ∩ GroupApproximation.Dynamics.chainRecurrentSet T ⊆
        Subtype.val '' GroupApproximation.Dynamics.chainRecurrentSet
          (GroupApproximation.ChainCore.firstReturnHomeomorph hC) :=
  GroupApproximation.ChainCore.DynamicRankBudget.printedInducedCoreCorner_closed X T r C hC

#audit_axioms manuscriptSentence_inducedCoreReturnRingCornerOfLEF

/-- **tex 1745–1747**, "Conversely, saturating that core through the finite towers gives a closed
invariant subsystem whose ring is a corner of a matrix ring over an LEF ring, hence LEF": the
saturation `Y' = returnSaturation T C CR(S_C)` is closed and `T`-invariant, and for every finite
field `k` the ring `R_{Y'}` is isomorphic to a corner `e M_N(A) e` with `A` LEF, and is LEF. -/
theorem manuscriptSentence_coreSaturationCornerOfMatrixOverLEF
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : GroupApproximation.ChainCore.IsReturnSection T r C) :
    IsClosed (GroupApproximation.ChainCore.returnSaturation T C
        (GroupApproximation.Dynamics.chainRecurrentSet
          (GroupApproximation.ChainCore.firstReturnHomeomorph hC))) ∧
      T '' GroupApproximation.ChainCore.returnSaturation T C
          (GroupApproximation.Dynamics.chainRecurrentSet
            (GroupApproximation.ChainCore.firstReturnHomeomorph hC)) =
        GroupApproximation.ChainCore.returnSaturation T C
          (GroupApproximation.Dynamics.chainRecurrentSet
            (GroupApproximation.ChainCore.firstReturnHomeomorph hC)) ∧
      ∀ (k : Type) [Field k] [Finite k],
        (∃ (N : ℕ) (A : Type) (_ : Ring A) (e : Matrix (Fin N) (Fin N) A) (he : IsIdempotentElem e),
          GroupApproximation.Pestov91.IsLEFRing A ∧
            Nonempty (GroupApproximation.ClopenCrossedProduct
                (GroupApproximation.ClopenCrossedProduct.restrictHomeo T
                  (GroupApproximation.ChainCore.image_returnSaturation
                    (GroupApproximation.Dynamics.chainRecurrentSet
                      (GroupApproximation.ChainCore.firstReturnHomeomorph hC)))) k ≃+*
              GroupApproximation.MFQuotientUnits.Corner (Matrix (Fin N) (Fin N) A) e he)) ∧
          GroupApproximation.Pestov91.IsLEFRing
            (GroupApproximation.ClopenCrossedProduct
              (GroupApproximation.ClopenCrossedProduct.restrictHomeo T
                (GroupApproximation.ChainCore.image_returnSaturation
                  (GroupApproximation.Dynamics.chainRecurrentSet
                    (GroupApproximation.ChainCore.firstReturnHomeomorph hC)))) k) :=
  GroupApproximation.ChainCore.DynamicRankBudget.printedCoreSaturationLEF_closed X T r C hC

#audit_axioms manuscriptSentence_coreSaturationCornerOfMatrixOverLEF

/-- **tex 1747–1749**, "Theorem~\ref{thm:core-ring-reflection} applied to this subsystem makes every
one of its points chain recurrent in $X$, proving the reverse inclusion": the saturation of `CR(S_C)`
lies in `CR(T)`, hence `CR(S_C) ⊆ C ∩ CR(T)`. -/
theorem manuscriptSentence_coreSaturationChainRecurrent
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : GroupApproximation.ChainCore.IsReturnSection T r C) :
    GroupApproximation.ChainCore.returnSaturation T C
        (GroupApproximation.Dynamics.chainRecurrentSet
          (GroupApproximation.ChainCore.firstReturnHomeomorph hC)) ⊆
        GroupApproximation.Dynamics.chainRecurrentSet T ∧
      Subtype.val '' GroupApproximation.Dynamics.chainRecurrentSet
          (GroupApproximation.ChainCore.firstReturnHomeomorph hC) ⊆
        C ∩ GroupApproximation.Dynamics.chainRecurrentSet T :=
  GroupApproximation.ChainCore.DynamicRankBudget.printedCoreSaturationRecurrent_closed X T r C hC

#audit_axioms manuscriptSentence_coreSaturationChainRecurrent

/-- **tex 1749–1750**, "The return transient ideal is therefore $J=p_CIp_C$": under the return ring
isomorphism `R_{S_C} ≃+* P_C = p_C R_X p_C`, an element `c` of the return ring lies in the transient
ideal `J` of `(C, S_C)` exactly when its image is `p_C a p_C` for some `a ∈ I`. -/
theorem manuscriptSentence_returnTransientIdealEqCornerOfI
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : GroupApproximation.ChainCore.IsReturnSection T r C)
    [CompactSpace C] (k : Type) [Field k] [Finite k]
    (c : GroupApproximation.ClopenCrossedProduct (GroupApproximation.ChainCore.firstReturnHomeomorph hC) k) :
    (∃ a ∈ GroupApproximation.ClopenCrossedProduct.coreTransientIdeal T k,
        ((GroupApproximation.ChainCore.returnRingEquiv k hC c :
            GroupApproximation.ChainCore.ReturnCorner k hC) : GroupApproximation.ClopenCrossedProduct T k) =
          GroupApproximation.ChainCore.returnP k hC * a * GroupApproximation.ChainCore.returnP k hC) ↔
      c ∈ GroupApproximation.ClopenCrossedProduct.coreTransientIdeal
        (GroupApproximation.ChainCore.firstReturnHomeomorph hC) k :=
  GroupApproximation.ChainCore.DynamicRankBudget.printedReturnTransientIdeal_closed X T r C hC k c

#audit_axioms manuscriptSentence_returnTransientIdealEqCornerOfI

end GroupApproximation.Manuscript.NonMF.RankBudget
