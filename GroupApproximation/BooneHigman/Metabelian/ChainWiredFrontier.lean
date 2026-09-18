import GroupApproximation.BooneHigman.Metabelian.ChainWiredAffine
import GroupApproximation.BooneHigman.Metabelian.ChainWiredEnvelope
import GroupApproximation.BooneHigman.Metabelian.ChainFiveStableK2
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsFreeClosed
import GroupApproximation.BooneHigman.Metabelian.AbsorptionEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVar
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabRange
import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Coords
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain wiring, part 3: the metabelian root from the open frontier (lane `bh-met-27`)

This module wires every landed `_of_` reduction and every landed closer of the
`fp-metabelian-groups-satisfy-boone-higman` tree into one endpoint whose hypotheses are exactly the
smallest open gap Statements on disk.

**Closed leaves used (no hypotheses):**
* `CharPCoords.charPPolynomialCoordinates` (char-`p` polynomial coordinates);
* `affineExtensionFPStatement_holds` (`ChainWiredAffine`, from lane `bh-met-05`);
* `CharPHost.TreeHost.charPAffineSelfSimilarStatement_holds` (char-`p` self-similar host);
* `CharZeroHost.charZeroAffineSelfSimilarStatement` (char-zero self-similar host).

**Reductions used:** positive characteristic through `charPLinearHostStatement_of_chain`,
characteristic zero through `charZeroLinearHostStatement_of_chainFive` (the rank-at-least-five
chain, so `ElemFPCharZero.CharZeroRankFourFPStatement` is not needed), the pieces through
`Coprimary.metabelianPieces_of_linearity` (so `Chain.CoprimaryLinearQuotientsStatement` is not
needed; the pure-characteristic splitting `exists_pureCharacteristic_split` is proved), and the
envelope through `fpSelfSimilarEnvelope_of_frontier` (`ChainWiredEnvelope`).

**The frontier (15 open Statements):**
1. `Coprimary.PureCharPrimeSplitStatement`: linearity in characteristic `p` of f.g. subgroups of
   split extensions `B ⋊ Q` (bh-met-26);
2. `Coprimary.PureCharLinearityZeroStatement`: linearity of f.g. metabelian groups with torsion-free
   derived subgroup (bh-met-19);
3. `Absorption.PolynomialSuslinStatement`: `SL_N ⊆ E_N` over `F_p[s]` and `ℤ[1/m][t]`, `N ≥ 3`;
4. `ElemFP.PolyK2StabRangeDiagStatement`: injective `K₂` stability on `ker ev₀` at `N = k + 4`;
5. `ElemFP.PolyK2OneVarNilStatement`: the one-variable nil part of `K₂(N, F_p[s])`;
6. `ElemFP.FieldK2VanishingStatement`: `K₂(N, F_p) = 0` for `N ≥ 5` (bh-met-15);
7. `CharZeroHost.FGSubringCoordinatesStatement`: f.g. subrings of char-zero fields embed in
   matrices over `ℤ[1/m][t]`;
8. `ElemFPCharZero.CharZeroStableK2FGStatement`: `K₂(N, ℤ[1/m][t])` is f.g. for `N ≥ k + 4, 5`;
9. `Envelope.HigmanVFinSectionStatement` and 10. `Envelope.RNFreeSectionCoreStatement`: finite
   presentation of Röver–Nekrashevych groups;
11. `Envelope.RNCommutatorFiniteIndexStatement`: `[V, V]` has finite index;
12. `Envelope.RNDisplaceStatement`, 13. `Envelope.RNCompressStatement`,
    14. `Envelope.RNFragmentsStatement`: simplicity of `[V, V]`;
15. `Envelope.RNWreathEmbedStatement`: Zaremsky's wreath embedding.

Among equivalent alternatives the refined name is used: `PolyK2OneVarNilStatement` for
`PolyK2NilPosStatement` (`ElemFP.polyK2NilPos_of_oneVar`), `PolyK2StabRangeDiagStatement` for
`PolyK2NilStabilityPosStatement` (`ElemFP.polyK2NilStabilityPos_of_diag`), the three clauses for
`RNDisplaceCompressStatement` (`Envelope.rnDisplaceCompress_of_clauses`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The positive-characteristic linear host from Suslin's theorem and the three `K₂` gaps. -/
theorem charPLinearHostStatement_of_frontier (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement) : CharPLinearHostStatement :=
  charPLinearHostStatement_of_chain CharPCoords.charPPolynomialCoordinates
    (Absorption.charPElementaryAbsorptionStatement_of_suslin hS)
    (ElemFP.polynomialFpElementaryFP_of_polynomialFpK2Vanishing
      (ElemFP.polynomialFpK2Vanishing_of_stabRangeDiag hdiag (ElemFP.polyK2NilPos_of_oneVar hone)
        hfield))
    affineExtensionFPStatement_holds CharPHost.TreeHost.charPAffineSelfSimilarStatement_holds

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.charPLinearHostStatement_of_frontier

/-- The characteristic-zero linear host from Suslin's theorem, the f.g.-subring coordinates and
finite generation of stable `K₂`. -/
theorem charZeroLinearHostStatement_of_frontier (hS : Absorption.PolynomialSuslinStatement)
    (hfg : CharZeroHost.FGSubringCoordinatesStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement) : CharZeroLinearHostStatement :=
  charZeroLinearHostStatement_of_chainFive (CharZeroHost.coordinatesStatement_of_fgSubring hfg)
    (Absorption.charZeroElementaryAbsorptionStatement_of_suslin hS)
    (charZeroElementaryFPFive_of_stableK2FG hK2) affineExtensionFPStatement_holds
    CharZeroHost.charZeroAffineSelfSimilarStatement

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.charZeroLinearHostStatement_of_frontier

/-- The linear host node (`Products.LinearHostStatement`) from frontier items 3–8. -/
theorem linearHostStatement_of_frontier (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hfg : CharZeroHost.FGSubringCoordinatesStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement) : Products.LinearHostStatement :=
  linearHostStatement_of_charP_charZero (charPLinearHostStatement_of_frontier hS hdiag hone hfield)
    (charZeroLinearHostStatement_of_frontier hS hfg hK2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.linearHostStatement_of_frontier

/-- The metabelian pieces node (`Products.MetabelianPiecesStatement`) from frontier items 1–8. -/
theorem metabelianPiecesStatement_of_frontier (hsplit : Coprimary.PureCharPrimeSplitStatement)
    (hzero : Coprimary.PureCharLinearityZeroStatement) (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hfg : CharZeroHost.FGSubringCoordinatesStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement) : Products.MetabelianPiecesStatement :=
  Coprimary.metabelianPieces_of_linearity (Coprimary.pureCharLinearity_of_split_zero hsplit hzero)
    (linearHostStatement_of_frontier hS hdiag hone hfield hfg hK2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.metabelianPiecesStatement_of_frontier

/-- **The root from the open frontier**: finitely presented metabelian groups satisfy the
Boone–Higman conjecture, given exactly the fifteen open gap Statements listed in the module
docstring (items 1–2 linearity, 3–8 linear hosts, 9–15 the self-similar envelope). -/
theorem finitelyPresentedMetabelianStatement_of_frontier
    (hsplit : Coprimary.PureCharPrimeSplitStatement)
    (hzero : Coprimary.PureCharLinearityZeroStatement) (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hfg : CharZeroHost.FGSubringCoordinatesStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement)
    (hV : Envelope.HigmanVFinSectionStatement) (hcore : Envelope.RNFreeSectionCoreStatement)
    (hfi : Envelope.RNCommutatorFiniteIndexStatement) (hD : Envelope.RNDisplaceStatement)
    (hC : Envelope.RNCompressStatement) (hF : Envelope.RNFragmentsStatement)
    (hw : Envelope.RNWreathEmbedStatement) : FinitelyPresentedMetabelianStatement :=
  Products.finitelyPresentedMetabelianStatement_of_pieces
    (metabelianPiecesStatement_of_frontier hsplit hzero hS hdiag hone hfield hfg hK2)
    (fpSelfSimilarEnvelope_of_frontier hV hcore hfi hD hC hF hw)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_frontier

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
