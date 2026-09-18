import GroupApproximation.Manuscript.NonMF.TorsionFreeJointNotions.Statements
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.GGT.AcylindricallyHyperbolicOsin
import GroupApproximation.GGT.OsinLimitSetSpelling
import GroupApproximation.Meta.AxiomGuard

/-!
# The joint torsion-free endpoint at the limit-set notion, over the Greendlinger waist

`non_mf_groups_exist.tex`, `thm:torsion-free` (tex line 297) and
`cor:regular-nonmf-algebra` (tex line 2204), for the same `Q`, at the limit-set notion
`GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet`
(`TorsionFreeJointNotions.PrintedTorsionFreeTheoremWithRegularAlgebraLimitSet`).

## Proof route

* `printedTorsionFreeTheoremWithRegularAlgebraLimitSet_of_printedLimitSet`: take `Q`
  from `TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet` and unpack
  `IsTwoGenerated Q` into `g₁ g₂`.  Hull's notion, which
  `TorsionFreeJoint.regularAlgebraClauses` needs as an instance, comes in two steps.
  First, limit set to Osin's notion: `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`
  (Osin's Theorem 1.1, excluding the lineal case, proved in `GGT/OsinLinealExclusion`).
  Second, Osin's notion to Hull's: `(GGT.isAcylindricallyHyperbolic_iff_osin Q).mpr`.
* `printedTorsionFreeTheoremWithRegularAlgebraLimitSet_of_greendlinger`: feed it
  `TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger`.

## Manuscript status

The one binder is `hgreendlinger`, Osin's Lemma 4.4 at least-area diagrams (the excluded
Greendlinger leaf).  Once that has a closed producer, applying it closes the endpoint.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeJointNotions

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace

/-- The printed theorem at the limit-set notion gives the joint statement at the
limit-set notion: the corollary's C⋆ clauses hold for the theorem's own `Q`. -/
theorem printedTorsionFreeTheoremWithRegularAlgebraLimitSet_of_printedLimitSet
    (h : TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet) :
    PrintedTorsionFreeTheoremWithRegularAlgebraLimitSet := by
  obtain ⟨Q, instQ, ⟨g₁, g₂, hgen⟩, hfp, htf, hlim, hT, hkill, hquot⟩ := h
  letI := instQ
  haveI := hfp
  haveI : IsAcylindricallyHyperbolic Q :=
    (GGT.isAcylindricallyHyperbolic_iff_osin Q).mpr
      (GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet Q hlim)
  exact ⟨Q, instQ, g₁, g₂, hgen, hfp, htf, hlim, hT, hkill, hquot,
    TorsionFreeJoint.regularAlgebraClauses Q htf hkill hgen⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeJointNotions.printedTorsionFreeTheoremWithRegularAlgebraLimitSet_of_printedLimitSet

/-- **`thm:torsion-free` with `cor:regular-nonmf-algebra` for the same `Q`, at the
limit-set notion, over the least-area Greendlinger waist** (tex lines 297 and 2204). -/
theorem printedTorsionFreeTheoremWithRegularAlgebraLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedTorsionFreeTheoremWithRegularAlgebraLimitSet :=
  printedTorsionFreeTheoremWithRegularAlgebraLimitSet_of_printedLimitSet
    (TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
      hgreendlinger)

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeJointNotions.printedTorsionFreeTheoremWithRegularAlgebraLimitSet_of_greendlinger

end TorsionFreeJointNotions
end NonMF
end Manuscript
end GroupApproximation
