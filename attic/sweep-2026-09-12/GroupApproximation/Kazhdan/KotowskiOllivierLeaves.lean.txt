import GroupApproximation.Kazhdan.GHBHyperbolicDiscCounts
import GroupApproximation.Kazhdan.GHBSharpExistenceSystolic
import GroupApproximation.Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# The Kotowski--Ollivier input from `GHB(7)`, over the zip, fold and fixed-clique leaves

`TheoremC.KotowskiOllivierStatement` is `Hyperbolic.SharpExistence`, the hyperbolic property (T)
input of the Fournier-Facio paragraph ("Fournier-Facio constructs a finitely presented torsion-free
group $G_0$ with property~\textup{(T)} ... \cite[\S2]{FFF}", tex line 1675), and the binder `hKO` of
every endpoint of `TorsionFreeLiteratureInputsLeastArea`.  With `GHB(7)` as the witness it reduces
to three open leaves:

* `hzip : Systolic.ZipSpurStatement CCKW.cosetComplex`, HC3(d), zipping a boundary backtrack of a
  triangulated disc (lane kh-torsion);
* `hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex`, HC6, folding away a mirror pair of inner
  triangles (lane fff-periodic);
* `hT6 : CCKW.SystolicInvariantCliqueStatement`, the fixed-clique theorem for systolic complexes
  (lane kh-cckw).

`KotowskiOllivierLeaves.kotowskiOllivierStatement_of_leaves` composes
`GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold` (filling from simple connectivity, the typed count
and the boundary sums spent) with `sharpExistence_ghb7_of_fixedCliqueHyp` (property (T), the orders
of `U₃(7)`, `U₄(7)` and Tits' lemma spent).  The `_of_hullKOLeaves` theorems restate the endpoints
of `TorsionFreeLiteratureInputsLeastArea` with `hKO` replaced by the three leaves.  Once the leaves
are proved, the closed `TheoremC.KotowskiOllivierStatement` is one application.

## Manuscript status

Scaffold over open leaves: `hzip`, `hfold`, `hT6`, and the other open hypotheses of
`TorsionFreeLiteratureInputsLeastArea`.  No endpoint is closed here.
-/

namespace GroupApproximation
namespace KMSGroup
namespace KotowskiOllivierLeaves

/-- **The hyperbolic property (T) input of [FFF §2], from `GHB(7)`**, over the zip move, the mirror
fold and the fixed-clique theorem. -/
theorem kotowskiOllivierStatement_of_leaves (hzip : Systolic.ZipSpurStatement CCKW.cosetComplex)
    (hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex)
    (hT6 : CCKW.SystolicInvariantCliqueStatement) :
    Manuscript.NonMF.TheoremC.KotowskiOllivierStatement :=
  sharpExistence_ghb7_of_fixedCliqueHyp hT6
    (GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold hzip hfold)

end KotowskiOllivierLeaves
end KMSGroup

namespace Manuscript
namespace NonMF
namespace TorsionFreeKOLeaves

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-- **The five literature inputs of the Fournier-Facio paragraph** (tex lines 1675–1685), over the
least-area leaves, with the Kotowski–Ollivier input taken from `GHB(7)` over `hzip`, `hfold`,
`hT6`. -/
theorem literatureInputs_of_leastAreaKOLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hzip : GroupApproximation.Systolic.ZipSpurStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hfold :
      GroupApproximation.Systolic.MirrorFoldStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement) :
    TheoremC.LiteratureInputs :=
  TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves hgreendlinger hbridge
    (GroupApproximation.KMSGroup.KotowskiOllivierLeaves.kotowskiOllivierStatement_of_leaves hzip
      hfold hT6)

/-- **The Fournier-Facio paragraph** (tex lines 1675–1685), from the least-area leaves, the
Kotowski–Ollivier leaves `hzip`, `hfold`, `hT6` of `GHB(7)`, and a finitely presented infinite
simple torsion-free group. -/
theorem fournierFacioParagraph_of_leastAreaKOLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hzip : GroupApproximation.Systolic.ZipSpurStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hfold :
      GroupApproximation.Systolic.MirrorFoldStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) : FournierFacioParagraph :=
  TorsionFreeLiteratureInputsLeastArea.fournierFacioParagraph_of_leastAreaLeaves hgreendlinger
    hbridge
    (GroupApproximation.KMSGroup.KotowskiOllivierLeaves.kotowskiOllivierStatement_of_leaves hzip
      hfold hT6) hW

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), over the least-area leaves and the
Kotowski–Ollivier leaves `hzip`, `hfold`, `hT6` of `GHB(7)`. -/
theorem manuscriptTorsionFreeTheorem_of_hullKOLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hzip : GroupApproximation.Systolic.ZipSpurStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hfold :
      GroupApproximation.Systolic.MirrorFoldStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) : PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves hgreendlinger
    hbridge
    (GroupApproximation.KMSGroup.KotowskiOllivierLeaves.kotowskiOllivierStatement_of_leaves hzip
      hfold hT6) hW

/-- **`thm:torsion-free` in the radical form**, over the same inputs. -/
theorem manuscriptTorsionFreeFullMFRadical_of_hullKOLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hzip : GroupApproximation.Systolic.ZipSpurStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hfold :
      GroupApproximation.Systolic.MirrorFoldStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    hgreendlinger hbridge
    (GroupApproximation.KMSGroup.KotowskiOllivierLeaves.kotowskiOllivierStatement_of_leaves hzip
      hfold hT6) hW

/-- **`cor:regular-nonmf-algebra`, along the printed proof** (tex line 1718), over the same inputs,
Dahmani–Guirardel–Osin's Theorem 2.35 at its source hypothesis and Gerasimova–Osin's Theorem 1.1. -/
theorem manuscriptRegularNonMFAlgebra_of_hullKOLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hzip : GroupApproximation.Systolic.ZipSpurStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hfold :
      GroupApproximation.Systolic.MirrorFoldStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves hgreendlinger
    hbridge
    (GroupApproximation.KMSGroup.KotowskiOllivierLeaves.kotowskiOllivierStatement_of_leaves hzip
      hfold hT6) hW hDGO hGO

/-- **`thm:torsion-free` at Osin's notion**, over the same inputs. -/
theorem manuscriptTorsionFreeTheoremOsin_of_hullKOLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hzip : GroupApproximation.Systolic.ZipSpurStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hfold :
      GroupApproximation.Systolic.MirrorFoldStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    hgreendlinger hbridge
    (GroupApproximation.KMSGroup.KotowskiOllivierLeaves.kotowskiOllivierStatement_of_leaves hzip
      hfold hT6) hW

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, over the same inputs. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_hullKOLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hzip : GroupApproximation.Systolic.ZipSpurStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hfold :
      GroupApproximation.Systolic.MirrorFoldStatement GroupApproximation.KMSGroup.CCKW.cosetComplex)
    (hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    hgreendlinger hbridge
    (GroupApproximation.KMSGroup.KotowskiOllivierLeaves.kotowskiOllivierStatement_of_leaves hzip
      hfold hT6) hW hDGO hGO

end TorsionFreeKOLeaves
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.KotowskiOllivierLeaves.kotowskiOllivierStatement_of_leaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.literatureInputs_of_leastAreaKOLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.fournierFacioParagraph_of_leastAreaKOLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptTorsionFreeTheorem_of_hullKOLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptTorsionFreeFullMFRadical_of_hullKOLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptRegularNonMFAlgebra_of_hullKOLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptTorsionFreeTheoremOsin_of_hullKOLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeKOLeaves.manuscriptRegularNonMFAlgebraOsin_of_hullKOLeaves
