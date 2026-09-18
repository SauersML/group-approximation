import GroupApproximation.Manuscript.MFRecognition.SeedClosed.Leaf
import GroupApproximation.GreendlingerClosedAll.Pending
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:seed` over the four open frontier Statements of the Greendlinger leaf

Lane gl-assembly-10, second module.  `mf_recognition_complexity.tex`, `lem:seed` (census row
c6172bdc109a): "Theorem~C of~\cite{NonMF} gives a finitely presented torsion-free group with no
nontrivial homomorphism to an MF group; such a group is not MF unless it is trivial, and it is not.
Fix one finite presentation code $P_-$ for this group."

`SeedClosed.manuscriptSentence_seedNotMF_of_greendlinger` (module `SeedClosed.Leaf`) takes the whole
Greendlinger leaf `RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}` as input.  The
leaf reduces, by the proved `GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier`
(`GreendlingerClosedAll/Pending`), to `ClosedAll.OpenFrontierStatement`: the conjunction of the four
region gaps of residuals 04, 06, 07 and 10.  This module composes the two, so the seed rests on
exactly those four Statements.  The hypothesis is strictly smaller in proof content than the leaf
(the budget, the closed trio, the monogon corner and the non-rose step are supplied), and it is
true, since each conjunct is a waist input of Osin's Lemma 4.4.

This module is kept separate from `SeedClosed.Leaf` so that the leaf-level reduction and the
unconditional existence statement do not import the Greendlinger leaf tree, which has never been
compiled.  Once gl-assembly-04 lands, the lane target `manuscriptSentence_seedNotMF` is
`manuscriptSentence_seedNotMF_of_greendlinger AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0, 0, 0}`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace SeedClosed

open PresentationCodes

/-- **`lem:seed`, printed proof, over the four open frontier Statements** (tex 667-676): with the
Greendlinger leaf read from `ClosedAll.OpenFrontierStatement` and the bridge and
Kotowski--Ollivier inputs closed, the seed code of Theorem C's group presents a non-MF group. -/
theorem manuscriptSentence_seedNotMF_of_openFrontier
    (hfrontier : GGT.VanKampen.GreendlingerLeaf.ClosedAll.OpenFrontierStatement.{0, 0, 0}) :
    ¬ IsOperatorMF (Carrier (SeedFromTheoremC.seedCodeC
      (GGT.VanKampen.GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier
        hfrontier)
      HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
      KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed)) :=
  manuscriptSentence_seedNotMF_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier
      hfrontier)

/-- **`lem:seed` as an existence statement, printed proof, over the four open frontier
Statements.** -/
theorem manuscriptSentence_seedExists_of_openFrontier
    (hfrontier : GGT.VanKampen.GreendlingerLeaf.ClosedAll.OpenFrontierStatement.{0, 0, 0}) :
    ∃ c : PresentationCode, ¬ IsOperatorMF (Carrier c) :=
  manuscriptSentence_seedExists_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier
      hfrontier)

end SeedClosed
end MFRecognition
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.MFRecognition.SeedClosed.manuscriptSentence_seedNotMF_of_openFrontier
#audit_axioms GroupApproximation.Manuscript.MFRecognition.SeedClosed.manuscriptSentence_seedExists_of_openFrontier
