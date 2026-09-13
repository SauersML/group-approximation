import GroupApproximation.Manuscript.NonMF.TheoremCAssemblyFoldLeaf
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.GGT.SystolicDiscMirrorFold
import GroupApproximation.Meta.AxiomGuard

/-!
# Theorem C over the least-area relative Greendlinger leaf

`TheoremCAssemblyFoldLeaf` states both printed forms of Theorem C over three
leaves: `hgreendlinger`, `hbridge` and the mirror-fold leaf.  Two of them are now
closed:
* `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`
  (`GGT/HullSCLemma51EmbeddedBridgeHolds.lean`) proves the bridge leaf;
* `Systolic.mirrorFold` (`GGT/SystolicDiscMirrorFold.lean`) proves
  `Systolic.MirrorFoldStatement X` for every triangle complex `X`.

This module applies both, so both forms stand over `hgreendlinger` alone.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

/-- **Theorem C (`thm:torsion-free`), in radical form**, over the least-area
relative Greendlinger leaf alone. -/
theorem manuscriptTorsionFreeFullMFRadical_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical_of_leastAreaFold hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    fun _ X => Systolic.mirrorFold X

/-- **Theorem C, in the simplified printed statement**, over the same leaf. -/
theorem manuscriptTorsionFreeSimplified_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedTorsionFreeSimplified :=
  manuscriptTorsionFreeSimplified_of_leastAreaFold hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    fun _ X => Systolic.mirrorFold X

end TheoremC
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeSimplified_of_greendlinger
