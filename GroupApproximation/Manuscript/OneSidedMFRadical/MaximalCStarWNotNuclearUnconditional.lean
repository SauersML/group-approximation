import GroupApproximation.Analysis.LanceMaximalNuclear
import GroupApproximation.Manuscript.OneSidedMFRadical.MaximalCStarWNotNuclear
import GroupApproximation.Meta.AxiomGuard

/-!
# `C^*_{\max}(W)` is not nuclear, with no quotient permanence

## The printed sentence

`non_mf_groups_exist.tex`, introduction, in the paragraph after
Theorem `thm:amenable-trace` (anchor string "is not nuclear, since"):

> Tikuisis, White, and Winter proved that faithful traces on separable nuclear
> `C^*`-algebras satisfying the universal coefficient theorem are
> quasidiagonal; here `C^*_{\max}(W)` is not nuclear, since `W` is not amenable.

## What changed

`MaximalCStarWNotNuclear.manuscriptMaximalCStarWNotNuclear_of_quotient` carried
the clause over `NuclearCStarQuotientInput` (nuclearity passes to quotients,
the Choi--Effros lifting theorem at the approximation property), because the
only route in the tree went through the reduced algebra.
`Analysis/LanceMaximalNuclear` proves Lance's theorem at the maximal algebra
directly: nuclearity of `C^*_{\max}(G)` gives almost invariant vectors from
the canonical trace and a Choi factorization, with no quotient.  So the printed
sentence is carried here with no hypothesis, at the corpus-wide predicate
`CStarExactness.IsNuclearCStarAlgebra` (the completely positive approximation
property), and along the printed reason: nonamenability.

The first clause of the sentence (Tikuisis--White--Winter) is attribution: the
manuscript uses it only to explain why a nonnuclear algebra is needed.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Amenability CStarExactness LiteralNonMFLinearWitness

/-- **The printed implication.**  For every discrete group, if `G` is not
amenable then `C^*_{\max}(G)` is not nuclear. -/
theorem manuscriptMaximalCStarNotNuclearOfNotAmenable :
    ∀ (G : Type) [Group G], ¬ IsAmenable G →
      ¬ IsNuclearCStarAlgebra (MaximalGroupCStar G) :=
  fun _ _ hG ↦
    LanceMaximal.not_isNuclearCStarAlgebra_maximalGroupCStar_of_not_isAmenable hG

/-- **Printed sentence** (introduction, after `thm:amenable-trace`):
"here `C^*_{\max}(W)` is not nuclear, since `W` is not amenable."

`W` is `WitnessGroup`, the concrete affine--Clifford witness of Section
`sec:amenable-nonqd` (the group of `thm:amenable-trace`).  Both clauses, and the
implication between them, are closed. -/
theorem manuscriptSentence_maximalCStarWNotNuclear :
    ¬ IsAmenable WitnessGroup ∧
      ¬ IsNuclearCStarAlgebra (MaximalGroupCStar WitnessGroup) :=
  ⟨WitnessGroupNonamenable.witnessGroup_not_isAmenable,
    manuscriptMaximalCStarNotNuclearOfNotAmenable WitnessGroup
      WitnessGroupNonamenable.witnessGroup_not_isAmenable⟩

/-- The printed clause alone. -/
theorem manuscriptMaximalCStarWNotNuclear :
    ¬ IsNuclearCStarAlgebra (MaximalGroupCStar WitnessGroup) :=
  manuscriptSentence_maximalCStarWNotNuclear.2

end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMaximalCStarNotNuclearOfNotAmenable

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_maximalCStarWNotNuclear

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMaximalCStarWNotNuclear
