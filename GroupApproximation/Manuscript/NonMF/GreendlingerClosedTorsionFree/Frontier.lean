import GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.Theorem
import GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.Intro
import GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.GroupAlgebra
import GroupApproximation.GreendlingerClosedAll.Pending
import GroupApproximation.Meta.AxiomGuard

/-!
# The torsion-free carriers over the four open frontier Statements of the Greendlinger leaf

Lane gl-assembly-07, audit module.  `non_mf_groups_exist.tex`, tex 66, 292, 297, 303 and 2204
(`thm:torsion-free`, Theorem C, `cor:regular-nonmf-algebra`):

> There is a two-generated, finitely presented, torsion-free, acylindrically hyperbolic group `Q`
> with property (T) such that every homomorphism from `Q` to an MF group is trivial.

The carriers of `GreendlingerClosedTorsionFree.{Theorem, Intro, GroupAlgebra}` take the whole leaf
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`.  The leaf reduces, by
the proved `GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier`
(`GreendlingerClosedAll/Pending`), to `ClosedAll.OpenFrontierStatement`, the conjunction of the four
region gaps of residuals 04, 06, 07 and 10.  This module composes the two.

The hypothesis `OpenFrontierStatement.{0, 0, 0}` is strictly smaller in proof content than the
leaf (the budget, the monogon corner and the non-rose step are supplied by hypothesis-free
producers), and it is true, since each conjunct is a waist input of Osin's Lemma 4.4.  Once
gl-assembly-04 lands, every carrier is closed by applying
`AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0, 0, 0}` to its `_of_greendlinger` form.

## Manuscript status

Partial on the four frontier Statements only.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree

/-- **The eight carriers of `thm:torsion-free`, Theorem C and `cor:regular-nonmf-algebra`**
(tex 297, 2204), over the four open frontier Statements. -/
theorem torsionFreeCarriers_of_openFrontier
    (hfrontier : GGT.VanKampen.GreendlingerLeaf.ClosedAll.OpenFrontierStatement.{0, 0, 0}) :
    TorsionFreeCarriersStatement :=
  torsionFreeCarriers_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier
      hfrontier)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.torsionFreeCarriers_of_openFrontier

/-- **tex 66 and tex 292**, over the four open frontier Statements. -/
theorem introCarriers_of_openFrontier
    (hfrontier : GGT.VanKampen.GreendlingerLeaf.ClosedAll.OpenFrontierStatement.{0, 0, 0}) :
    IntroCarriersStatement :=
  introCarriers_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier
      hfrontier)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.introCarriers_of_openFrontier

/-- **tex 303**, for the group of `thm:torsion-free`, over the four open frontier Statements. -/
theorem torsionFreeGroupAlgebra_of_openFrontier
    (hfrontier : GGT.VanKampen.GreendlingerLeaf.ClosedAll.OpenFrontierStatement.{0, 0, 0}) :
    PrintedTorsionFreeGroupAlgebra :=
  manuscriptSentence_torsionFreeGroupAlgebra_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier
      hfrontier)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.torsionFreeGroupAlgebra_of_openFrontier

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree
