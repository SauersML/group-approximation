import GroupApproximation.Manuscript.SimpleKazhdanSofic.FinitelyPresentedRecursivePresentation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HostInstancePieces
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemReducesToLanguageInstance
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFLamplighterCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# The instances in the last statement of `cor:host`: closed

`simple_kazhdan_sofic_group.tex` at origin/main 8b36733d7, `cor:host` (census key `9b1a6e7489a1`,
tex l.310–313):

> So one such group contains every recursively presented finitely generated LEF group, for instance
> every finitely presented residually finite group and every $G_Y$ with $L(Y)$ recursive
> (Corollary~\ref{cor:wp}).

The assemblies are in `LEFHostInstances`. This module feeds them closed producers:

* `finitelyPresentedRecursivePresentationStatement` (`FinitelyPresentedRecursivePresentation`);
* `genValueGeneratesStatement` (`HostInstancePieces`);
* `printedSimpleKazhdanSoficMain` (`SimpleKazhdanSoficMainClosed`, `thm:main`);
* skf-degrees' `printedWordProblemReducesToLanguage` (`WordProblemReducesToLanguageInstance`).

Declarations:

* `printedFinitelyPresentedRFInstance : PrintedFinitelyPresentedRFInstance`, closed;
* `printedRecursiveLanguageInstance : PrintedRecursiveLanguageInstance`, closed;
* `printedRecursivelyPresentedLEFHostInstances_of_lamplighterHost`: the whole sentence over
  sk-lef-assembly's `LamplighterHostStatement`, the concrete lamplighter host, through
  `lefLamplighterStatement_of_host`. sk-lef-action's `printedLamplighterHost` is meant to supply it.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- **Every finitely presented residually finite group** is finitely generated, recursively
presented and LEF (tex l.311–312). -/
theorem printedFinitelyPresentedRFInstance : PrintedFinitelyPresentedRFInstance :=
  printedFinitelyPresentedRFInstance_of_pieces finitelyPresentedRecursivePresentationStatement

/-- **Every `G_Y` with `L(Y)` recursive** is finitely generated, recursively presented and LEF
(tex l.312–313). -/
theorem printedRecursiveLanguageInstance : PrintedRecursiveLanguageInstance :=
  printedRecursiveLanguageInstance_of_pieces printedSimpleKazhdanSoficMain
    printedWordProblemReducesToLanguage genValueGeneratesStatement

/-- **The last statement of `cor:host`, with its instances** (tex l.310–313), over the concrete
lamplighter host. -/
theorem printedRecursivelyPresentedLEFHostInstances_of_lamplighterHost
    (hhost : LamplighterHostStatement) : PrintedRecursivelyPresentedLEFHostInstances :=
  printedRecursivelyPresentedLEFHostInstances_of_pieces
    (printedRecursivelyPresentedLEFHost_of_lamplighter (lefLamplighterStatement_of_host hhost))
    printedFinitelyPresentedRFInstance printedRecursiveLanguageInstance

end SimpleKazhdanSofic
end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedFinitelyPresentedRFInstance
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedRecursiveLanguageInstance
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedRecursivelyPresentedLEFHostInstances_of_lamplighterHost
