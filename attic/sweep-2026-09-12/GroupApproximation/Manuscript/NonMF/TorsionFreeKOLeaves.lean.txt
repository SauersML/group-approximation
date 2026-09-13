import GroupApproximation.Kazhdan.GHBSharpExistenceSystolic
import GroupApproximation.Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# The torsion-free endpoints over the fixed-clique and hyperbolicity leaves of `GHB(7)`

`TorsionFreeLiteratureInputsLeastArea` states the literature inputs, the Fournier-Facio paragraph
and the section's endpoints over open hypotheses.  One of them is
`hKO : TheoremC.KotowskiOllivierStatement`, which is `Hyperbolic.SharpExistence`: the hyperbolic
property (T) input behind "Fournier-Facio constructs a finitely presented torsion-free group $G_0$
with property~\textup{(T)} ... \cite[\S2]{FFF}" (tex line 1675).

This module takes `GHB(7)` as the witness, through `KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp`
(`Kazhdan/GHBSharpExistenceSystolic`: property (T), the orders of `U₃(7)`, `U₄(7)` and Tits' lemma
are already proved there), and restates each endpoint with `hKO` replaced by two open leaves:

* `hT6 : KMSGroup.CCKW.SystolicInvariantCliqueStatement`, the fixed-clique theorem for systolic
  complexes (lane kh-cckw);
* `hhyp : Hyperbolic.IsHyperbolicGroup (KMSGroup.GHB 7)`, CCKW Theorem 3.1(i).  Its producer
  `KMSGroup.GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold` (`Kazhdan/GHBHyperbolicDiscCounts`) takes
  the zip and fold moves; `Kazhdan/KotowskiOllivierLeaves` states the endpoints over those.

## Manuscript status

Scaffold over open leaves.  Every theorem carries `hT6` and `hhyp`, and the other open hypotheses of
`TorsionFreeLiteratureInputsLeastArea` (`hgreendlinger`, `hbridge`, `hW`, and `hDGO`, `hGO` where
those forms have them).  No endpoint is closed here.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeKOLeaves

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-- **The five literature inputs of the Fournier-Facio paragraph** (tex lines 1675–1685), over the
least-area leaves, with the Kotowski–Ollivier input taken from `GHB(7)` over `hT6` and `hhyp`. -/
theorem literatureInputs_of_leastAreaFixedCliqueHyp
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hhyp :
      GroupApproximation.Hyperbolic.IsHyperbolicGroup (GroupApproximation.KMSGroup.GHB 7)) :
    TheoremC.LiteratureInputs :=
  TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves hgreendlinger hbridge
    (GroupApproximation.KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp hT6 hhyp)

/-- **The Fournier-Facio paragraph** (tex lines 1675–1685), from the least-area leaves, the
Kotowski–Ollivier leaves `hT6`, `hhyp` of `GHB(7)`, and a finitely presented infinite simple
torsion-free group. -/
theorem fournierFacioParagraph_of_leastAreaFixedCliqueHyp
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hhyp :
      GroupApproximation.Hyperbolic.IsHyperbolicGroup (GroupApproximation.KMSGroup.GHB 7))
    (hW : FinitelyPresentedInfiniteSimpleStatement) : FournierFacioParagraph :=
  TorsionFreeLiteratureInputsLeastArea.fournierFacioParagraph_of_leastAreaLeaves hgreendlinger
    hbridge (GroupApproximation.KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp hT6 hhyp) hW

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), over the least-area leaves and the
Kotowski–Ollivier leaves `hT6`, `hhyp` of `GHB(7)`. -/
theorem manuscriptTorsionFreeTheorem_of_hullFixedCliqueHyp
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hhyp :
      GroupApproximation.Hyperbolic.IsHyperbolicGroup (GroupApproximation.KMSGroup.GHB 7))
    (hW : FinitelyPresentedInfiniteSimpleStatement) : PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves hgreendlinger
    hbridge (GroupApproximation.KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp hT6 hhyp) hW

/-- **`thm:torsion-free` in the radical form**, over the same inputs. -/
theorem manuscriptTorsionFreeFullMFRadical_of_hullFixedCliqueHyp
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hhyp :
      GroupApproximation.Hyperbolic.IsHyperbolicGroup (GroupApproximation.KMSGroup.GHB 7))
    (hW : FinitelyPresentedInfiniteSimpleStatement) :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    hgreendlinger hbridge
    (GroupApproximation.KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp hT6 hhyp) hW

/-- **`cor:regular-nonmf-algebra`, along the printed proof** (tex line 1718), over the same inputs,
Dahmani–Guirardel–Osin's Theorem 2.35 at its source hypothesis and Gerasimova–Osin's Theorem 1.1. -/
theorem manuscriptRegularNonMFAlgebra_of_hullFixedCliqueHyp
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hhyp :
      GroupApproximation.Hyperbolic.IsHyperbolicGroup (GroupApproximation.KMSGroup.GHB 7))
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves hgreendlinger
    hbridge (GroupApproximation.KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp hT6 hhyp) hW hDGO
    hGO

/-- **`thm:torsion-free` at Osin's notion**, over the same inputs. -/
theorem manuscriptTorsionFreeTheoremOsin_of_hullFixedCliqueHyp
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hhyp :
      GroupApproximation.Hyperbolic.IsHyperbolicGroup (GroupApproximation.KMSGroup.GHB 7))
    (hW : FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    hgreendlinger hbridge
    (GroupApproximation.KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp hT6 hhyp) hW

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, over the same inputs. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_hullFixedCliqueHyp
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hhyp :
      GroupApproximation.Hyperbolic.IsHyperbolicGroup (GroupApproximation.KMSGroup.GHB 7))
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    hgreendlinger hbridge
    (GroupApproximation.KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp hT6 hhyp) hW hDGO hGO

end TorsionFreeKOLeaves
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.literatureInputs_of_leastAreaFixedCliqueHyp
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.fournierFacioParagraph_of_leastAreaFixedCliqueHyp
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptTorsionFreeTheorem_of_hullFixedCliqueHyp
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptTorsionFreeFullMFRadical_of_hullFixedCliqueHyp
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptRegularNonMFAlgebra_of_hullFixedCliqueHyp
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptTorsionFreeTheoremOsin_of_hullFixedCliqueHyp
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptRegularNonMFAlgebraOsin_of_hullFixedCliqueHyp
