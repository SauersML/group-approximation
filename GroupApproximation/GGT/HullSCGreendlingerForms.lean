import GroupApproximation.GGT.HullSCLemma44BoundedLeastAreaCanonical
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.GGT.HullSCTheorem71GeneralLeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Theorem 7.1 chain over the least-area Greendlinger leaf alone

The Hull chain behind `thm:hull` (`non_mf_groups_exist.tex` line 1636, `\label{thm:hull}`)
is stated over two leaves:
* the least-area Greendlinger waist `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`;
* the embedded bridge `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`.

The bridge is proved by `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`
(`GGT/HullSCLemma51EmbeddedBridgeHolds.lean`), so each form here applies it and stands over
`hgreendlinger` alone.  The forms come from:
* `HullSCTheorem71GeneralLeastArea`: the canonical quotient, one step, tower and ball form of
  Theorem 7.1, at every ambient group;
* `HullSCLemma44BoundedLeastAreaCanonical`: the bounded canonical Lemma 4.4, the torsion-free
  canonical quotient and one step.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **Hull's canonical quotient at every ambient group** (tex line 1636, `\label{thm:hull}`),
over the least-area Greendlinger leaf alone. -/
theorem hullCanonicalQuotientStatementGeneral_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullCanonicalQuotientStatementGeneral.{0} :=
  hullCanonicalQuotientStatementGeneral_of_leastAreaLeaves hgreendlinger
    relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **One step of Hull's Theorem 7.1 at every ambient group** (tex line 1636,
`\label{thm:hull}`), over the least-area Greendlinger leaf alone. -/
theorem hullOneStepStatementGeneral_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullOneStepStatementGeneral.{0} :=
  hullOneStepStatementGeneral_of_leastAreaLeaves hgreendlinger
    relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **The tower of Hull's Theorem 7.1 at every ambient group** (tex line 1636,
`\label{thm:hull}`), over the least-area Greendlinger leaf alone. -/
theorem hullTowerStatementGeneral_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullTowerStatementGeneral.{0} :=
  hullTowerStatementGeneral_of_leastAreaLeaves hgreendlinger
    relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **Hull's Theorem 7.1 in ball form at every ambient group** (tex line 1636,
`\label{thm:hull}`), over the least-area Greendlinger leaf alone. -/
theorem hullBallFormStatementGeneral_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullBallFormStatementGeneral.{0} :=
  hullBallFormStatementGeneral_of_leastAreaLeaves hgreendlinger
    relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **Hull's Lemma 4.4 in canonical bounded form**, behind `\label{thm:hull}` (tex line 1636),
over the least-area Greendlinger leaf alone, through the least-area spelling waist. -/
theorem boundedHullLemma44CanonicalQuotientStatement_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    BoundedHullLemma44CanonicalQuotientStatement.{0} :=
  boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea
    (relativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement_of_leastAreaGreendlinger
      hgreendlinger relativeDiscRealizationSpellingStatement
      relativeExteriorArcConversionAtWordRotatedStatement)
    relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **Hull's canonical quotient at a torsion-free ambient group** (tex line 1636,
`\label{thm:hull}`), over the least-area Greendlinger leaf alone. -/
theorem torsionFreeHullCanonicalQuotientStatement_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeHullCanonicalQuotientStatement.{0} :=
  torsionFreeHullCanonicalQuotientStatement_of_leastAreaLeaves hgreendlinger
    relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **One step of Hull's Theorem 7.1 at a torsion-free ambient group** (tex line 1636,
`\label{thm:hull}`), over the least-area Greendlinger leaf alone. -/
theorem hullOneStepStatement_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullOneStepStatement.{0} :=
  hullOneStepStatement_of_leastAreaLeaves hgreendlinger
    relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.hullCanonicalQuotientStatementGeneral_of_greendlinger
#audit_axioms GroupApproximation.HullSC.hullOneStepStatementGeneral_of_greendlinger
#audit_axioms GroupApproximation.HullSC.hullTowerStatementGeneral_of_greendlinger
#audit_axioms GroupApproximation.HullSC.hullBallFormStatementGeneral_of_greendlinger
#audit_axioms GroupApproximation.HullSC.boundedHullLemma44CanonicalQuotientStatement_of_greendlinger
#audit_axioms GroupApproximation.HullSC.torsionFreeHullCanonicalQuotientStatement_of_greendlinger
#audit_axioms GroupApproximation.HullSC.hullOneStepStatement_of_greendlinger
