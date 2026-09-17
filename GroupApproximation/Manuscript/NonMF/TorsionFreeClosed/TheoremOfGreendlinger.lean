import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:torsion-free` and "apply `lem:saturation`", over the least-area Greendlinger leaf

`non_mf_groups_exist.tex`, tex 297 (`\label{thm:torsion-free}`):

> There is a two-generated, finitely presented, torsion-free, acylindrically hyperbolic
> group `Q` with property (T) such that every homomorphism from `Q` to an MF group is
> trivial.  In particular, no nontrivial quotient of `Q` is MF.

and tex 2182 (proof of `thm:torsion-free`):

> By Lemma `lem:saturation` applied to `G₀` and `N`, there is a surjective homomorphism
> `φ : G₀ → Q` with `Q` two-generated, finitely presented, torsion-free, and
> acylindrically hyperbolic, and `φ(N) = Q`.

## Route

Lane nm-torsionfree-04.  Every wall of the torsion-free section is closed in the corpus
except `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (Osin's Lemma
4.4 at least-area diagrams), whose closer
`GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea` lives in
`GreendlingerLeaf/Assembly.lean`, which is not importable yet.  So each endpoint below
takes that one leaf as its single binder `hgreendlinger` and applies the corresponding
`TorsionFreeGreendlingerLeaf.*_of_greendlinger` reduction.  Once the assembly lands,
each endpoint closes by applying it to
`GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

/-- **`thm:torsion-free`, as printed** (tex 297), from the least-area Greendlinger leaf. -/
theorem manuscriptSentence_torsionFreeTheorem_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger hgreendlinger

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_torsionFreeTheorem_of_greendlinger

/-- **`thm:torsion-free` at Osin's notion of acylindrical hyperbolicity** (tex 297). -/
theorem manuscriptSentence_torsionFreeTheorem_osin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremOsin_of_greendlinger hgreendlinger

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_torsionFreeTheorem_osin_of_greendlinger

/-- **`thm:torsion-free` at the limit-set notion of acylindrical hyperbolicity** (tex 297). -/
theorem manuscriptSentence_torsionFreeTheorem_limitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger hgreendlinger

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_torsionFreeTheorem_limitSet_of_greendlinger

/-- **`thm:torsion-free` in the full-MF-radical form** `TheoremC.PrintedTorsionFreeFullMFRadical`
(tex 297). -/
theorem manuscriptSentence_torsionFreeFullMFRadical_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeFullMFRadical_of_greendlinger hgreendlinger

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_torsionFreeFullMFRadical_of_greendlinger

/-- **"By Lemma `lem:saturation` applied to `G₀` and `N`, there is a surjective homomorphism
`φ : G₀ → Q` ..."** (tex 2182, proof of `thm:torsion-free`). -/
theorem manuscriptSentence_theoremApplySaturation_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger hgreendlinger

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_theoremApplySaturation_of_greendlinger

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation
