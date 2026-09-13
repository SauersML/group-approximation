import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionRotate
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import GroupApproximation.Meta.AxiomGuard

/-!
# A following boundary cycle lies in one face class of the walk

A boundary cycle of a face set follows its boundary when each dart reaches the next by one face
step and rotations around internal darts (`BoundaryCycle.FollowsBoundary`).  Such a rotation
crosses an internal edge.  Internal darts and their reverses are never on the cycle, so the step
is a face-class step off the edges of the cycle.  Hence all darts of a following boundary cycle lie
in one face class of the walk (`CombMap.FaceClassStep` with `walkKeep` of the cycle).

For a simple closed walk this is `IsSimpleClosedWalk.eqvGen_of_mem`
(`Estimating/OsinAppendixEulerTwoGonPocketFaces`).  A noncrossing walk whose inner cycle follows
its boundary, such as the lake of `OsinPocketLakeModel`, need not be simple, and this module covers
it.  That is the hypothesis `connected` of `TwoGonWalkHyp`.

* `BoundaryCycle.eqvGen_boundaryPerm_of_followsBoundary`: a dart and its successor are in one face
  class.
* `BoundaryCycle.eqvGen_of_mem_of_followsBoundary`: every two darts of the cycle are.
* `IsNoncrossingClosedWalk.eqvGen_of_mem_of_innerFollows`: the same for a noncrossing walk whose
  inner cycle follows its boundary.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(a)); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen

open Surgery.MapCollapse SimpleClosedWalkSides

universe u

namespace Surgery.MapCollapse.BoundaryCycle

variable {M : CombMap.{u}} {faces : Finset M.Face}

/-- **A dart of a following boundary cycle and its successor lie in one face class of the
walk.**  The boundary walk is one face step, then rotations around internal darts.  A rotation
`σ u = facePerm (α u)` crosses the internal edge of `u`, which is off the cycle. -/
theorem eqvGen_boundaryPerm_of_followsBoundary (boundary : BoundaryCycle M faces)
    (hwalk : boundary.FollowsBoundary) (x : BoundaryDart M faces) :
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M boundary.cycle)) x.1
      (boundary.boundaryPerm x).1 := by
  have hstep : ∀ y, Relation.ReflTransGen (fun u v => InternalDart M faces u ∧ M.sigma u = v)
      (M.facePerm x.1) y →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M boundary.cycle)) x.1 y := by
    intro y hy
    induction hy with
    | refl => exact .rel _ _ (Or.inl rfl)
    | @tail b c _ huv ih =>
        obtain ⟨hint, rfl⟩ := huv
        obtain ⟨hin, halpha⟩ := hint
        have hnot : ¬ walkKeep M boundary.cycle b := by
          rintro (hmem | hmem)
          · obtain ⟨-, hout⟩ := (boundary.cycle_mem_iff b).mp hmem
            exact hout halpha
          · obtain ⟨-, hout⟩ := (boundary.cycle_mem_iff (M.alpha b)).mp hmem
            rw [M.alpha_involutive b] at hout
            exact hout hin
        refine .trans _ _ _ ih (.trans _ _ _ (.rel _ _ (Or.inr ⟨hnot, rfl⟩)) (.rel _ _ (Or.inl ?_)))
        change M.sigma b = M.sigma (M.alpha (M.alpha b))
        rw [M.alpha_involutive b]
  exact hstep _ (hwalk x)

/-- **Every two darts of a following boundary cycle lie in one face class of the walk.**  The
successor on the cycle is the cyclic permutation of the list, whose powers reach every dart. -/
theorem eqvGen_of_mem_of_followsBoundary (boundary : BoundaryCycle M faces)
    (hwalk : boundary.FollowsBoundary) {d e : M.Dart} (hd : d ∈ boundary.cycle)
    (he : e ∈ boundary.cycle) :
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M boundary.cycle)) d e := by
  classical
  have hnext : ∀ x (hx : x ∈ boundary.cycle),
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M boundary.cycle)) x
        (boundary.cycle.next x hx) := by
    intro x hx
    have h := boundary.eqvGen_boundaryPerm_of_followsBoundary hwalk
      ⟨x, (boundary.cycle_mem_iff x).mp hx⟩
    rwa [boundaryPerm_apply_val] at h
  have hpow : ∀ k : ℕ, (boundary.cycle.formPerm ^ k) d ∈ boundary.cycle ∧
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M boundary.cycle)) d
        ((boundary.cycle.formPerm ^ k) d) := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hd, by simpa using Relation.EqvGen.refl d⟩
    | succ k ih =>
        obtain ⟨hmem, hrel⟩ := ih
        rw [pow_succ', Equiv.Perm.mul_apply]
        refine ⟨List.formPerm_apply_mem_of_mem hmem, .trans _ _ _ hrel ?_⟩
        rw [List.formPerm_apply_mem_eq_next boundary.cycle_nodup _ hmem]
        exact hnext _ hmem
  obtain ⟨n, rfl⟩ :=
    boundary.cycle_nodup.isCycleOn_formPerm.exists_pow_eq' (Set.toFinite _) hd he
  exact (hpow n).2

end Surgery.MapCollapse.BoundaryCycle

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **The darts of a noncrossing walk whose inner cycle follows its boundary lie in one face class
of the walk.**  The inner cycle lists the walk itself. -/
theorem eqvGen_of_mem_of_innerFollows (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hin : (hw.innerCycle hM).FollowsBoundary) {d e : M.Dart} (hd : d ∈ w) (he : e ∈ w) :
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) d e :=
  (hw.innerCycle hM).eqvGen_of_mem_of_followsBoundary hin hd he

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.eqvGen_boundaryPerm_of_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.eqvGen_of_mem_of_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.eqvGen_of_mem_of_innerFollows
