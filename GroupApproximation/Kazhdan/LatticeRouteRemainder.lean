import GroupApproximation.Kazhdan.KazhdanFiniteIndex
import GroupApproximation.Algebra.FiniteIndexQuasiIsometry
import GroupApproximation.Algebra.ReidemeisterSchreier

/-!
# What the lattice route to `SharpExistence` still needs

`Kazhdan/SharpExistenceRoutes.lean` reduces `Hyperbolic.SharpExistence` --- an
infinite, finitely presented, torsion-free hyperbolic group with property `(T)`
--- to a cocompact lattice in `Sp(n,1)` together with **three** permanence
properties, all three of which it leaves open.  This module records what has
happened to them.

| permanence property | status |
| --- | --- |
| property `(T)` | **proved**, `FiniteIndex.kazhdanFiniteIndexPermanence` |
| hyperbolicity | reduced to the Morse lemma, `hyperbolicFiniteIndexPermanence_of_quasiIsometryInvariant` |
| finite presentation | reduced to Schreier's index formula, `finitePresentationFiniteIndexPermanence_of_freeInput` |

`sharpExistence_of_latticeRoute_of_inputs` is the resulting statement: the
lattice route now needs the lattice, plus exactly **two** general facts about
groups, neither of which is about property `(T)`:

* `Hyperbolic.QuasiIsometryInvariant` --- hyperbolicity is a quasi-isometry
  invariant, i.e. the Morse lemma (`Algebra/MorseLemma.lean` proves the
  rough-isometry case and exhibits the `K²` defect that blocks the general one);
* `FiniteIndex.FreeFiniteIndexFinitelyPresented` --- a finite-index subgroup of a
  finitely generated free group is finitely presented, i.e. Nielsen--Schreier
  with a finite rank (Mathlib has the freeness but not the rank).

Both are theorems of the literature and neither is assumed here: every statement
below takes its inputs explicitly, and `Hyperbolic.SharpExistence` remains
unproved in this repository.
-/

namespace GroupApproximation
namespace FiniteIndex

/-- **Hyperbolicity passes to finite-index subgroups**, given quasi-isometry
invariance.  The prose claim of `Kazhdan/SharpExistenceRoutes.lean` --- that
`Hyperbolic.HyperbolicFiniteIndexPermanence` "is an instance of
`Hyperbolic.QuasiIsometryInvariant`" --- as a theorem. -/
theorem hyperbolicFiniteIndexPermanence_of_quasiIsometryInvariant
    (h : Hyperbolic.QuasiIsometryInvariant) :
    Hyperbolic.HyperbolicFiniteIndexPermanence := by
  intro Γ inst Λ hfi hΓ
  exact @isHyperbolicGroup_subgroup_of_quasiIsometryInvariant h Γ inst Λ hfi hΓ

/-- **Finite presentation passes to finite-index subgroups**, given the free
case.  Reidemeister--Schreier, from `Algebra/ReidemeisterSchreier.lean`. -/
theorem finitePresentationFiniteIndexPermanence_of_freeInput
    (hfree : FreeFiniteIndexFinitelyPresented) :
    Hyperbolic.FinitePresentationFiniteIndexPermanence := by
  intro Γ inst Λ hfi hΓ
  exact @isFinitelyPresented_subgroup_of_finiteIndex.{0} hfree Γ inst Λ hfi hΓ

/-- **The lattice route, with the property `(T)` input discharged and the other
two reduced to named literature facts.**

Compare `Hyperbolic.sharpExistence_of_latticeRoute`, which takes all three
permanence properties as hypotheses.  What is left is the Morse lemma, the
Schreier index formula, and the lattice itself. -/
theorem sharpExistence_of_latticeRoute_of_inputs
    (hmorse : Hyperbolic.QuasiIsometryInvariant)
    (hfree : FreeFiniteIndexFinitelyPresented)
    (L : Hyperbolic.LatticeRouteInput) : Hyperbolic.SharpExistence :=
  Hyperbolic.sharpExistence_of_latticeRoute
    (hyperbolicFiniteIndexPermanence_of_quasiIsometryInvariant hmorse)
    kazhdanFiniteIndexPermanence
    (finitePresentationFiniteIndexPermanence_of_freeInput hfree) L

end FiniteIndex
end GroupApproximation
