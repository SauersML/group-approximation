import GroupApproximation.CharClass.ParityEvenFlagCompact
import GroupApproximation.CharClass.ChernFactorBridge
import GroupApproximation.CharClass.ChernSplitRelation
import GroupApproximation.CharClass.ChernSliceNaturality

/-!
# `HasSplitting` for a bundle over a compact base, from the flag relation

`Wu.SplittingData` asks for five things; four of them are now discharged from the
tower, and this file assembles them so that the only remaining input is the split
relation on the flag total space.

* `pull_injective` — `flagProj_map_injective_compact`, unconditional.
* `hsq` — `cc-bundle`'s `projPi_comp_projComap`, which is `rfl`.
* `htaut` — `cc-projective`'s `LH.tautEulerOf_comap`.  Note it is stated in the
  direction `pull … = tautEulerOf (comap …)`, so it rewrites the right-hand side
  after `TotalH.map_of`.  Proving it by definitional equality instead does not
  work: the two bundles are definitionally equal, but verifying that unfolds a
  subtype of a product of matrices and exhausts the heartbeat budget, and
  rewriting the ingredients first is a dependent rewrite through
  `eulerOfBundle`'s trace argument.  Their route goes through the classifying
  map and never asks the question.
* the two rank conditions — `rfl`, since `lerayHirschData_of_graded` sets the rank.

What is left is `hrel`, the split relation for the pullback to the flag, which is
`cc-steenrod`'s.  Note the shape of `root` here: it is a **parameter**, agreeing
with the line Euler classes only where the relation looks at it.  Quantifying the
trace condition over all indices instead is unsatisfiable at the flag, because
`trace_flagLine` holds only below the flag height and the line family is forced to
zero above it.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Wu

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.LHCast

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- The bundle pulled back to the flag total space. -/
abbrev flagPullback (p : Bundle X ι) (r : ℕ) : Bundle (Bundle.Flag p r) ι :=
  Bundle.comap (Bundle.flagProj p r) p

theorem rank_flagPullback (p : Bundle X ι) (r : ℕ) (hrank : ∀ x, p.rank x = r)
    (w : Bundle.Flag p r) : (flagPullback p r).rank w = r :=
  hrank (Bundle.flagProj p r w)

/-- **`Wu.HasSplitting` from the flag split relation.**  Every field but the split
relation is discharged here. -/
theorem hasSplitting_of_flagSplitRelation [DecidableEq ι] [CompactSpace X] [Nonempty X]
    [Nontrivial (TotalH (TopCat.of X))]
    (p : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r) (hrank : ∀ x, p.rank x = r)
    [CompactSpace (Bundle.Flag p r)] [Nonempty (Bundle.Flag p r)]
    [Nontrivial (TotalH (TopCat.of (Bundle.Flag p r)))]
    (root : ℕ → Hmod2 (TopCat.of (Bundle.Flag p r)) 2)
    (hroot : ∀ l : ℕ, ∃ (d : ℕ) (g : TopCat.of (Bundle.Flag p r) ⟶ CPtop d)
      (h : Hmod2 (CPtop d) 2), root l = pull g 2 h)
    (hrel : (lerayHirschData_of_graded (lerayHirschGraded_compact (flagPullback p r) r
        (rank_flagPullback p r hrank) hr1)).SplitRelation r root) :
    Wu.HasSplitting (TopCat.of X)
      (lerayHirschData_of_graded (lerayHirschGraded_compact p r hrank hr1)).chern := by
  refine hasSplitting_of_splitRelation
    (lerayHirschData_of_graded (lerayHirschGraded_compact p r hrank hr1))
    (lerayHirschData_of_graded (lerayHirschGraded_compact (flagPullback p r) r
      (rank_flagPullback p r hrank) hr1))
    (cmap (Bundle.flagProj p r)) (cmap (Bundle.projComap (Bundle.flagProj p r) p))
    ?_ ?_ (flagProj_map_injective_compact p r hrank) r rfl rfl root hroot hrel
  · apply TopCat.ext
    intro z
    rfl
  · rw [TotalH.map_of]
    exact congrArg (TotalH.of (TopCat.of (Bundle.Proj (flagPullback p r))) 2)
      (LH.tautEulerOf_comap (Bundle.flagProj p r) p).symm

end

end Wu
end CharClass
end GroupApproximation
