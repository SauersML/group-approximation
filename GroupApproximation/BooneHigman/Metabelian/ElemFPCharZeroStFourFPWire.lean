import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPPhi
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroSLFourFPReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The Steinberg half, closed (bh-met-91m)

* `czStFourFP_stFour : czSLFourFP_StFourStatement`: `St_4(ℤ[1/m])` is finitely presented for
  every `m > 0` (`ElemFPCharZeroStFourFPPhi`).
* `czStFourFP_sl_of_k2Fng`: composed with `czSLFourFP_sl_of_st_of_k2Fng`, the `K₂` half
  `CZK2FngRankFourStatement` alone gives `czRankFourFP_SLFourStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- **The Steinberg half.** -/
theorem czStFourFP_stFour : czSLFourFP_StFourStatement := fun m hm =>
  czStFourFP_stFour_of_pos m hm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_stFour

/-- **Wire.**  The `K₂` half gives `SL_4(ℤ[1/m])` finitely presented. -/
theorem czStFourFP_sl_of_k2Fng (hk : CZK2FngRankFourStatement) :
    czRankFourFP_SLFourStatement :=
  czSLFourFP_sl_of_st_of_k2Fng czStFourFP_stFour hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_sl_of_k2Fng

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
