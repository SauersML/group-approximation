import GroupApproximation.BooneHigman.Metabelian.ChainFiveCharZero
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-at-least-five elementary leaf from finite generation of stable `K₂`

Lane `bh-met-25`.  Lane `bh-met-17` (`ElemFPCharZeroEndpoint.lean`) shows that `St_{d+5}(S)` is
finitely presented for `S = ℤ[1/m][t_0, ..., t_{k-1}]`, and that a finitely generated `K₂(N, S)`
makes `E_N(S)` finitely presented.  At rank `N ≥ 5` only
`ElemFPCharZero.CharZeroStableK2FGStatement` is needed.  The rank-four corner
`ElemFPCharZero.CharZeroRankFourFPStatement` is not needed.

**Warning.**  `K₂(N, S) = ⊥` is FALSE.  For example `{-1,-1} ≠ 1` in `K₂(ℤ[1/m])` for `m ≥ 1`, since
its real Hilbert symbol is `-1`.
Only finite generation is used.

Endpoints:
* `charZeroElementaryFPFive_of_stableK2FG`;
* `finitelyPresentedMetabelianStatement_of_chainStableK2`: the root from the eleven leaves, with
  `CharZeroStableK2FGStatement` in place of the elementary leaf.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- **The rank-at-least-five elementary leaf from finite generation of stable `K₂`.** -/
theorem charZeroElementaryFPFive_of_stableK2FG
    (h : ElemFPCharZero.CharZeroStableK2FGStatement) : CharZeroElementaryFPFiveStatement := by
  intro m k N hN h5
  obtain ⟨d, rfl⟩ : ∃ d, N = d + 5 := ⟨N - 5, by omega⟩
  haveI := ElemFPCharZero.steinbergSIntPoly_isFinitelyPresented m k d
  exact ElemFPCharZero.isFinitelyPresented_elementaryGroup_of_fg (h m k (d + 5) hN h5)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.charZeroElementaryFPFive_of_stableK2FG

/-- **The root from the leaves of the FRONTIER tree**, with the characteristic-zero elementary
leaf replaced by finite generation of stable `K₂`. -/
theorem finitelyPresentedMetabelianStatement_of_chainStableK2
    (hcop : CoprimaryLinearQuotientsStatement)
    (hcoordP : CharPCoords.CharPPolynomialCoordinatesStatement)
    (habsP : CharPElementaryAbsorptionStatement) (hfpP : ElemFP.PolynomialFpElementaryFPStatement)
    (hssP : CharPAffineSelfSimilarStatement)
    (hcoord0 : CharZeroPolynomialCoordinatesStatement)
    (habs0 : CharZeroElementaryAbsorptionStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement)
    (hss0 : CharZeroAffineSelfSimilarStatement) (haff : AffineExtensionFPStatement)
    (henv : Products.FPSelfSimilarEnvelopeStatement) :
    FinitelyPresentedMetabelianStatement :=
  finitelyPresentedMetabelianStatement_of_chainFive hcop hcoordP habsP hfpP hssP hcoord0 habs0
    (charZeroElementaryFPFive_of_stableK2FG hK2) hss0 haff henv

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_chainStableK2

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
