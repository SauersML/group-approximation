import GroupApproximation.Manuscript.NonMF.TheoremCAssemblyKOLeaves
import GroupApproximation.GGT.SystolicDiscZip
import GroupApproximation.Meta.AxiomGuard

/-!
# Theorem C over the least-area leaves and the mirror-fold leaf

`TheoremCAssemblyKOLeaves` states both printed forms of Theorem C over four
leaves: `hgreendlinger`, `hbridge`, and the zip and fold leaves of the coset
complex of `GHB(7)`.  The zip leaf is now closed:
`KMSGroup.CCKW.zipSpur_cosetComplex` (`GGT/SystolicDiscZip.lean`) proves
`Systolic.ZipSpurStatement CCKW.cosetComplex` for every triangle complex.  This
module applies it, so both forms stand over three leaves.

The fold leaf is taken in the shape `CCKW.systolicInvariantClique_of_zipFold`
consumes, `∀ (V : Type) (X : Systolic.TriangleComplex V), MirrorFoldStatement X`,
and is used here at `CCKW.cosetComplex`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

/-- **Theorem C (`thm:torsion-free`), in radical form**, over the two least-area
leaves and the mirror-fold leaf.  The zip leaf is `CCKW.zipSpur_cosetComplex`. -/
theorem manuscriptTorsionFreeFullMFRadical_of_leastAreaFold
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hfold : ∀ (V : Type) (X : Systolic.TriangleComplex V), Systolic.MirrorFoldStatement X) :
    PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical_of_leastAreaZipFold hgreendlinger hbridge
    KMSGroup.CCKW.zipSpur_cosetComplex (hfold _ KMSGroup.CCKW.cosetComplex)

/-- **Theorem C, in the simplified printed statement**, over the same three
leaves. -/
theorem manuscriptTorsionFreeSimplified_of_leastAreaFold
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hfold : ∀ (V : Type) (X : Systolic.TriangleComplex V), Systolic.MirrorFoldStatement X) :
    PrintedTorsionFreeSimplified :=
  manuscriptTorsionFreeSimplified_of_leastAreaZipFold hgreendlinger hbridge
    KMSGroup.CCKW.zipSpur_cosetComplex (hfold _ KMSGroup.CCKW.cosetComplex)

end TheoremC
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaFold
#audit_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaFold
