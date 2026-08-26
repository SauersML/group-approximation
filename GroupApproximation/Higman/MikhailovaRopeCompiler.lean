import GroupApproximation.Higman.MikhailovaGraphProductWitness
import GroupApproximation.Higman.RopeTrick

/-!
# Feeding the concrete Mikhailova witness into the rope trick

The preceding modules build an actual benign witness for the normal closure
of relators on the rank-three free group.  The repository already proves the
hard direction of Higman's benign-subgroup lemma internally: `RopeTrick`
turns any such witness into a finitely presented overgroup of the quotient.

This file records the direct composition.  It is a group-level construction,
not an effectivity claim: it does not yet compute a finite-presentation code
from an index for a recursively enumerable presentation.
-/

namespace GroupApproximation
namespace Higman
namespace MikhailovaRopeCompiler

open MikhailovaRankThree
open MikhailovaGraphProduct

/-- Finite marked embedding data alone give a finitely presented overgroup of
the source presented quotient.  The benign witness is the explicit
product-of-three-free-groups Mikhailova witness. -/
theorem nonempty_fpOvergroup_of_markedEmbedding
    {X : Type} [Finite X] (S : Set Source) {R : Set (FreeGroup X)}
    (hR : R.Finite) (words : Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R) (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S)) :
    Nonempty (FPOvergroup (PresentedGroup S)) := by
  let w := normalClosureWitnessOfMarkedEmbedding S hR words i hi hcomm
  exact fpOvergroup_of_benign ⟨w⟩

/-- The Mikhailova witness producted with an explicit finitely presented graph
factor gives the same finitely presented hull whenever the source relators
already lie in the graph kernel. -/
theorem nonempty_fpOvergroup_of_markedEmbedding_and_graph
    {X P : Type} [Finite X] [Group P] [Group.IsFinitelyPresented P]
    (S : Set Source) {R : Set (FreeGroup X)} (hR : R.Finite)
    (words : Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R) (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S))
    (q : Source →* P) (hSq : Subgroup.normalClosure S ≤ q.ker) :
    Nonempty (FPOvergroup (PresentedGroup S)) := by
  let w := normalClosureProductWitness S hR words i hi hcomm q hSq
  exact fpOvergroup_of_benign ⟨w⟩

/-- The graph target may itself be only embedded in a finitely presented
group.  No finite-presentability assumption is placed on that target. -/
theorem nonempty_fpOvergroup_of_markedEmbedding_and_embeddedGraph
    {X Q P : Type} [Finite X] [Group Q] [Group P]
    [Group.IsFinitelyPresented P]
    (S : Set Source) {R : Set (FreeGroup X)} (hR : R.Finite)
    (words : Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R) (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S))
    (q : Source →* Q) (j : Q →* P) (hj : Function.Injective j)
    (hSq : Subgroup.normalClosure S ≤ q.ker) :
    Nonempty (FPOvergroup (PresentedGroup S)) := by
  let w := normalClosureProductWitnessOfEmbeddedGraph
    S hR words i hi hcomm q j hj hSq
  exact fpOvergroup_of_benign ⟨w⟩

end MikhailovaRopeCompiler
end Higman
end GroupApproximation
