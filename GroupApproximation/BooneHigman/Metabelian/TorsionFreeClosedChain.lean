import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierTwo
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain wiring with characteristic-zero linearity discharged (lane bh-met-63)

`ChainWiredFrontierTwo.finitelyPresentedMetabelianStatement_of_frontierTwo` takes ten gap
Statements.  Item 2, `Coprimary.PureCharLinearityZeroStatement`, is now proved with no
hypotheses as `Coprimary.pureCharLinearityZero` (`TorsionFreeClosed`).

The variants below drop `hzero` and keep every other hypothesis identical (same names, types
and order):

* `metabelianPiecesStatement_of_frontierTwo_zeroClosed`: `metabelianPiecesStatement_of_frontierTwo`
  (`ChainWiredFrontierTwoBase.lean:50`) without `hzero`;
* `finitelyPresentedMetabelianStatement_of_frontierTwo_zeroClosed`:
  `finitelyPresentedMetabelianStatement_of_frontierTwo` (`ChainWiredFrontierTwo.lean:85`) without
  `hzero`.

**The remaining frontier (9 Statements)**:

1. `Coprimary.PureCharPrimeSplitStatement` (linearity in characteristic `p`);
2. `Absorption.PolynomialSuslinStatement`;
3. `ElemFP.PolyK2StabRangeDiagStatement`;
4. `ElemFP.PolyK2OneVarNilStatement`;
5. `ElemFP.FieldK2VanishingStatement`;
6. `ElemFPCharZero.CharZeroStableK2FGStatement`;
7. `Envelope.HigmanVFinSectionStatement`;
8. `Envelope.RNFreeSectionCoreStatement`;
9. `Envelope.RNCommutatorFiniteIndexStatement`.

No new mathematics: every proof is a term application of on-disk declarations.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The metabelian pieces node from the remaining linearity and linear-host gaps; linearity in
characteristic zero is `Coprimary.pureCharLinearityZero`. -/
theorem metabelianPiecesStatement_of_frontierTwo_zeroClosed
    (hsplit : Coprimary.PureCharPrimeSplitStatement) (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement) : Products.MetabelianPiecesStatement :=
  metabelianPiecesStatement_of_frontierTwo hsplit Coprimary.pureCharLinearityZero hS hdiag hone
    hfield hK2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.metabelianPiecesStatement_of_frontierTwo_zeroClosed

/-- **The root from the nine remaining gaps**: finitely presented metabelian groups satisfy the
Boone–Higman conjecture, given the nine Statements listed in the module docstring (item 1
linearity in characteristic `p`, items 2–6 linear hosts, items 7–9 the self-similar envelope). -/
theorem finitelyPresentedMetabelianStatement_of_frontierTwo_zeroClosed
    (hsplit : Coprimary.PureCharPrimeSplitStatement) (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement)
    (hV : Envelope.HigmanVFinSectionStatement) (hcore : Envelope.RNFreeSectionCoreStatement)
    (hfi : Envelope.RNCommutatorFiniteIndexStatement) : FinitelyPresentedMetabelianStatement :=
  finitelyPresentedMetabelianStatement_of_frontierTwo hsplit Coprimary.pureCharLinearityZero hS
    hdiag hone hfield hK2 hV hcore hfi

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_frontierTwo_zeroClosed

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
