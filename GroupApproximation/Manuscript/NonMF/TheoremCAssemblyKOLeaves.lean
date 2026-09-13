import GroupApproximation.Manuscript.NonMF.TheoremCAssembly
import GroupApproximation.Kazhdan.KotowskiOllivierClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Theorem C over the least-area leaves and the Kotowski–Ollivier leaves

`TheoremCAssembly` states Theorem C over three hypotheses: `hgreendlinger`,
`hbridge` and `hKO`.  `Kazhdan/KotowskiOllivierClosed.lean` reduces `hKO` to
three systolic leaves of the coset complex of `GHB(7)`:

* `hzip : Systolic.ZipSpurStatement CCKW.cosetComplex`, zipping a boundary
  backtrack of a triangulated disc;
* `hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex`, folding away a
  mirror pair of inner triangles;
* `hT6 : CCKW.SystolicInvariantCliqueStatement`, the fixed-clique theorem for
  systolic complexes.

This module composes the two, so both printed forms of Theorem C stand over five
named leaves and no `sorry`.  It is not in the root closure, because
`Kazhdan.KotowskiOllivierClosed` is not.  When `kotowskiOllivier_closed` lands,
the three systolic binders go by one application, and the forms in
`TheoremCAssembly` lose `hKO` the same way.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

/-- **Theorem C (`thm:torsion-free`), in radical form**, over the two least-area
leaves and the three systolic leaves of
`KotowskiOllivierClosed.kotowskiOllivier_of_leaves`. -/
theorem manuscriptTorsionFreeFullMFRadical_of_leastAreaKOLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hzip : Systolic.ZipSpurStatement KMSGroup.CCKW.cosetComplex)
    (hfold : Systolic.MirrorFoldStatement KMSGroup.CCKW.cosetComplex)
    (hT6 : KMSGroup.CCKW.SystolicInvariantCliqueStatement) :
    PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs hgreendlinger hbridge
    (KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_of_leaves hzip hfold hT6)

/-- **Theorem C, in the simplified printed statement**, over the same five
leaves. -/
theorem manuscriptTorsionFreeSimplified_of_leastAreaKOLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hzip : Systolic.ZipSpurStatement KMSGroup.CCKW.cosetComplex)
    (hfold : Systolic.MirrorFoldStatement KMSGroup.CCKW.cosetComplex)
    (hT6 : KMSGroup.CCKW.SystolicInvariantCliqueStatement) :
    PrintedTorsionFreeSimplified :=
  manuscriptTorsionFreeSimplified_of_leastAreaInputs hgreendlinger hbridge
    (KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_of_leaves hzip hfold hT6)

end TheoremC
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaKOLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaKOLeaves
