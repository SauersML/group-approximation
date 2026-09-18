import GroupApproximation.Manuscript.NonMF.TorsionFreeJointNotions.Statements
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.GGT.AcylindricallyHyperbolicOsin
import GroupApproximation.Meta.AxiomGuard

/-!
# The joint torsion-free endpoint at Osin's notion, over the Greendlinger waist

`non_mf_groups_exist.tex`, `thm:torsion-free` (tex line 297) and
`cor:regular-nonmf-algebra` (tex line 2204), for the same `Q`, at Osin's notion
`GGT.IsAcylindricallyHyperbolicOsin`
(`TorsionFreeJointNotions.PrintedTorsionFreeTheoremWithRegularAlgebraOsin`).

## Proof route

* `printedTorsionFreeTheoremWithRegularAlgebraOsin_of_printedOsin`: take `Q` from
  `TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin` and unpack `IsTwoGenerated Q`
  into `g₁ g₂`.  Hull's notion, which `TorsionFreeJoint.regularAlgebraClauses` needs as
  an instance, is `(GGT.isAcylindricallyHyperbolic_iff_osin Q).mpr`.  The C⋆ clauses
  then need only finite presentation, torsion-freeness and the MF-killing clause.
* `printedTorsionFreeTheoremWithRegularAlgebraOsin_of_greendlinger`: feed it
  `TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremOsin_of_greendlinger`.

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

/-- The printed theorem at Osin's notion gives the joint statement at Osin's notion:
the corollary's C⋆ clauses hold for the theorem's own `Q`. -/
theorem printedTorsionFreeTheoremWithRegularAlgebraOsin_of_printedOsin
    (h : TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin) :
    PrintedTorsionFreeTheoremWithRegularAlgebraOsin := by
  obtain ⟨Q, instQ, ⟨g₁, g₂, hgen⟩, hfp, htf, hosin, hT, hkill, hquot⟩ := h
  letI := instQ
  haveI := hfp
  haveI : IsAcylindricallyHyperbolic Q :=
    (GGT.isAcylindricallyHyperbolic_iff_osin Q).mpr hosin
  exact ⟨Q, instQ, g₁, g₂, hgen, hfp, htf, hosin, hT, hkill, hquot,
    TorsionFreeJoint.regularAlgebraClauses Q htf hkill hgen⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeJointNotions.printedTorsionFreeTheoremWithRegularAlgebraOsin_of_printedOsin

/-- **`thm:torsion-free` with `cor:regular-nonmf-algebra` for the same `Q`, at Osin's
notion, over the least-area Greendlinger waist** (tex lines 297 and 2204). -/
theorem printedTorsionFreeTheoremWithRegularAlgebraOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedTorsionFreeTheoremWithRegularAlgebraOsin :=
  printedTorsionFreeTheoremWithRegularAlgebraOsin_of_printedOsin
    (TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremOsin_of_greendlinger hgreendlinger)

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeJointNotions.printedTorsionFreeTheoremWithRegularAlgebraOsin_of_greendlinger

end TorsionFreeJointNotions
end NonMF
end Manuscript
end GroupApproximation
