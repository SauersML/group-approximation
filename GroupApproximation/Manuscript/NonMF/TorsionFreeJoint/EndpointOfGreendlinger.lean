import GroupApproximation.Manuscript.NonMF.TorsionFreeJoint.EndpointStatement
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:torsion-free` with `cor:regular-nonmf-algebra`, over the Greendlinger leaf

`non_mf_groups_exist.tex`, `thm:torsion-free` (tex lines 295-301) and
`cor:regular-nonmf-algebra` (tex lines 2203-2207), stated for one and the same
group `Q` as `TorsionFreeJoint.PrintedTorsionFreeTheoremWithRegularAlgebra`.

## Proof route

* `TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger` gives a
  `Q` with the seven printed clauses of `thm:torsion-free`; its binder is Osin's
  Lemma 4.4 at least-area diagrams,
  `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}`,
  which is still open: the Greendlinger lanes prove it only as
  `GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals`,
  over `P07InnerPocket.PocketFourPieceOffStatement` and
  `P10RoseExtremalTrim.RoseExtremalJunctionStatement`.
* Unpack `IsTwoGenerated Q` into `g₁ g₂`, install the finitely presented and
  acylindrically hyperbolic clauses as instances, and apply
  `TorsionFreeJoint.regularAlgebraClauses` to the torsion-free clause and the
  "every homomorphism to an MF group is trivial" clause.

The C⋆ half needs no hypothesis at all; the only binder is the one that
`thm:torsion-free` itself still carries in the corpus.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeJoint

/-- **`thm:torsion-free` and `cor:regular-nonmf-algebra` for the same `Q`**, over
Osin's least-area Greendlinger lemma (the one open binder of `thm:torsion-free`). -/
theorem printedTorsionFreeTheoremWithRegularAlgebra_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedTorsionFreeTheoremWithRegularAlgebra := by
  obtain ⟨Q, instQ, ⟨g₁, g₂, hgen⟩, hfp, htf, hacyl, hT, hkill, hquot⟩ :=
    TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger hgreendlinger
  letI := instQ
  haveI := hfp
  haveI := hacyl
  obtain ⟨hsep, hone, hu₁, hu₂, hclosure, hsimple, huniq, hsr, hsf, hnotMF⟩ :=
    regularAlgebraClauses Q htf hkill hgen
  exact ⟨Q, instQ, g₁, g₂, hgen, hfp, htf, hacyl, hT, hkill, hquot,
    hsep, hone, hu₁, hu₂, hclosure, hsimple, huniq, hsr, hsf, hnotMF⟩

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeJoint.printedTorsionFreeTheoremWithRegularAlgebra_of_greendlinger

end TorsionFreeJoint
end NonMF
end Manuscript
end GroupApproximation
