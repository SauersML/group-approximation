import GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.Leaf
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# The four printed proof-step propositions of `sec:torsion-free` over the five open residuals

`non_mf_groups_exist.tex`, Section `sec:torsion-free`:

* tex line 2129: "Hull's proof treats $m=1$ by passing to $G/\normal{r}_G$ for one element $r$ and
  the general case by induction on $m$, using his clause~(d), that $\varphi(N)$ is again
  suitable, so $\ker\varphi$ is the normal closure of $m$ elements and $Q$ is finitely presented
  when $G$ is."
* tex line 2144 (proof of `lem:saturation`): "By Hull, $N$ contains two elements $h_1,h_2$ such
  that $N_0=\langle h_1,h_2\rangle$ is suitable with respect to a generating set $A'\supseteq A$
  to which Hull's small cancellation theorem again applies.  Apply Theorem~\ref{thm:hull} to
  $N_0$, with respect to $A'$, with $g_1,\dots,g_m$ a finite generating set of $G$."
* tex line 2182 (proof of `thm:torsion-free`): "By Lemma~\ref{lem:saturation} applied to $G_0$
  and $N$, there is a surjective homomorphism $\varphi\colon G_0\to Q$ with $Q$ two-generated,
  finitely presented, torsion-free, and acylindrically hyperbolic, and $\varphi(N)=Q$."

The statements are the named propositions of `TorsionFreeSectionSentencesFourLeaves`, unchanged.

## Route

Each body is the matching `TorsionFreeGreendlingerLeaf.*_of_greendlinger` theorem applied to
`GreendlingerClosedSteps.leastAreaLeaf_of_openResidualsBelow hopen`.

## Manuscript status

Each theorem takes `hopen : AsmWaist.GreendlingerOpenResidualsBelowStatement.{0,0,0}`, the five
open residuals of the Below Greendlinger waist (see `GreendlingerClosedSteps/Leaf`).  So these
carriers are `partial`; they close once lane gl-assembly-04 produces the residuals.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GreendlingerClosedSteps

/-- **The paragraph after `thm:hull`, as printed** (tex line 2129), over the five open residuals
of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullProofParagraph_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

/-- **The pair `h₁, h₂` and `thm:hull` again** (tex line 2144, in the proof of
`lem:saturation`), over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_saturationPairAndHullAgain_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

/-- **"Apply Theorem `thm:hull` to `N₀`, with respect to `A'`, with `g₁,…,g_m` a finite
generating set of `G`"** (tex line 2144, in the proof of `lem:saturation`), over the five open
residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_saturationApplyHull_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

/-- **"By Lemma `lem:saturation` applied to `G₀` and `N`"** (tex line 2182, in the proof of
`thm:torsion-free`), over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_theoremApplySaturation_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

end GreendlingerClosedSteps
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_hullProofParagraph_of_openResidualsBelow
#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_saturationPairAndHullAgain_of_openResidualsBelow
#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_saturationApplyHull_of_openResidualsBelow
#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_theoremApplySaturation_of_openResidualsBelow
