import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFHostInstancesClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Meta.AxiomGuard

/-!
# The last statement of `cor:host`, with its instances: closed

`simple_kazhdan_sofic_group.tex` at origin/main 8b36733d7, `cor:host` (census key `9b1a6e7489a1`,
tex l.310–313):

> So one such group contains every recursively presented finitely generated LEF group, for instance
> every finitely presented residually finite group and every $G_Y$ with $L(Y)$ recursive
> (Corollary~\ref{cor:wp}).

`printedRecursivelyPresentedLEFHostInstances_of_lamplighterHost` (`LEFHostInstancesClosed`) proves the
sentence over sk-lef-assembly's `LamplighterHostStatement`. sk-lef-action's `printedLamplighterHost`
(`LamplighterHost`) proves that statement.

* `printedRecursivelyPresentedLEFHostInstances : PrintedRecursivelyPresentedLEFHostInstances`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- **The last statement of `cor:host`, with its instances** (tex l.310–313), closed. -/
theorem printedRecursivelyPresentedLEFHostInstances : PrintedRecursivelyPresentedLEFHostInstances :=
  printedRecursivelyPresentedLEFHostInstances_of_lamplighterHost printedLamplighterHost

end SimpleKazhdanSofic
end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedRecursivelyPresentedLEFHostInstances
