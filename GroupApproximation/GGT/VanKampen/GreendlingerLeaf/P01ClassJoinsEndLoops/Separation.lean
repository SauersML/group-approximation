import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.Pocket
import GroupApproximation.Meta.AxiomGuard

/-!
# End loops of the class producer: separation after a longest pocket

For a pocket `seg x J` of cell `i` (`1 ≤ J < n`), put `p = f^J x`, `u = f^(J-1) x` and
`w = f^(n-1) x`.  In the map `joined u w` the dart `p` does not reach `x` (`JunctionPocket.not_reach`),
and walking backwards along the face it reaches none of `x, …, f^(J-1) x`.  Hence every dart of
the cell reached from `p` is `f^a x` with `J ≤ a < n`, and every dart whose reverse lies on the
face of `α p` (a face other than the cell) is reached from `p`.

The module also records the arc and region cases of the route in `FaceOrbit.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

/-- Reachability in the map with the corners after `α u` and `α w` joined. -/
abbrev Reach (M : CombMap.{v}) (u w y z : M.Dart) : Prop :=
  Relation.EqvGen (FoldMap.joined M u w).Adjacent y z

theorem head?_seg {M : CombMap.{v}} (x : M.Dart) {l : ℕ} (hl : 0 < l) :
    (seg M x l).head? = some x := by
  cases l with
  | zero => exact (Nat.lt_irrefl 0 hl).elim
  | succ l => rw [seg_succ', List.head?_cons]

section Separation

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {i : Fin X.rCellCount}

/-- The dart after a pocket does not reach the base of the pocket. -/
theorem sep_not_reach {x u w : X.toCombMap.Dart} {J : ℕ} (hx : IsPocket X i x J) (hJ : 1 ≤ J)
    (hJn : J < (cellDarts X i).length)
    (hu : (X.toCombMap.facePerm ^ (J - 1)) x = u)
    (hw : (X.toCombMap.facePerm ^ ((cellDarts X i).length - 1)) x = w) :
    ¬ Reach X.toCombMap u w ((X.toCombMap.facePerm ^ J) x) x := by
  have hfu : X.toCombMap.facePerm u = (X.toCombMap.facePerm ^ J) x := by
    rw [← hu, ← pow_succ_apply x (J - 1), Nat.sub_add_cancel hJ]
  have hfw : X.toCombMap.facePerm w = x := by
    rw [← hw, ← pow_succ_apply x ((cellDarts X i).length - 1),
      Nat.sub_add_cancel (by omega : 1 ≤ (cellDarts X i).length), pow_length_cell hx.1]
  have hne : u ≠ w := by
    intro h
    rw [← hu, ← hw] at h
    have := pow_inj_cell hx.1 (by omega) (by omega) h
    omega
  have hface : X.toCombMap.faceOf u = X.toCombMap.faceOf w := by
    rw [← hu, ← hw, faceOf_pow, faceOf_pow]
  have hpinch : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha u) (X.toCombMap.alpha w) := by
    have h : X.toCombMap.sigma.SameCycle (X.toCombMap.facePerm w) (X.toCombMap.facePerm u) := by
      rw [hfu, hfw]
      exact hx.2.2.1
    have h' : X.toCombMap.sigma.SameCycle (X.toCombMap.sigma (X.toCombMap.alpha w))
        (X.toCombMap.sigma (X.toCombMap.alpha u)) := h
    exact (Equiv.Perm.sameCycle_apply_right.mp (Equiv.Perm.sameCycle_apply_left.mp h')).symm
  intro hreach
  have h := JunctionPocket.not_reach X.planar hne hface hpinch
  rw [hfu, hfw] at h
  exact h hreach

/-- The dart after a pocket reaches no dart of the pocket. -/
theorem not_reach_pow {x u w : X.toCombMap.Dart} {J : ℕ} (hx : IsPocket X i x J) (hJ : 1 ≤ J)
    (hJn : J < (cellDarts X i).length)
    (hu : (X.toCombMap.facePerm ^ (J - 1)) x = u)
    (hw : (X.toCombMap.facePerm ^ ((cellDarts X i).length - 1)) x = w) :
    ∀ j, j < J →
      ¬ Reach X.toCombMap u w ((X.toCombMap.facePerm ^ J) x) ((X.toCombMap.facePerm ^ j) x) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [pow_zero, Equiv.Perm.one_apply]
    exact sep_not_reach hx hJ hJn hu hw
  | succ j ih =>
    intro hj hreach
    have hne1 : (X.toCombMap.facePerm ^ j) x ≠ u := by
      intro h
      rw [← hu] at h
      have := pow_inj_cell hx.1 (by omega) (by omega) h
      omega
    have hne2 : (X.toCombMap.facePerm ^ j) x ≠ w := by
      intro h
      rw [← hw] at h
      have := pow_inj_cell hx.1 (by omega) (by omega) h
      omega
    have hadj : Reach X.toCombMap u w ((X.toCombMap.facePerm ^ j) x)
        ((X.toCombMap.facePerm ^ (j + 1)) x) := by
      rw [pow_succ_apply x j]
      exact JunctionPocket.joined_reach_facePerm hne1 hne2
    exact ih (by omega) (Relation.EqvGen.trans _ _ _ hreach (Relation.EqvGen.symm _ _ hadj))

/-- A dart of the cell reached from the dart after the pocket lies after the pocket. -/
theorem outside_index {x u w z : X.toCombMap.Dart} {J : ℕ} (hx : IsPocket X i x J) (hJ : 1 ≤ J)
    (hJn : J < (cellDarts X i).length)
    (hu : (X.toCombMap.facePerm ^ (J - 1)) x = u)
    (hw : (X.toCombMap.facePerm ^ ((cellDarts X i).length - 1)) x = w)
    (hz : z ∈ cellDarts X i) (hr : Reach X.toCombMap u w ((X.toCombMap.facePerm ^ J) x) z) :
    ∃ a, J ≤ a ∧ a < (cellDarts X i).length ∧ (X.toCombMap.facePerm ^ a) x = z := by
  obtain ⟨a, ha, rfl⟩ := exists_pow_cell hx.1 hz
  refine ⟨a, ?_, ha, rfl⟩
  by_contra hlt
  exact not_reach_pow hx hJ hJn hu hw a (by omega) hr

/-- Darts whose reverses sit on the face of `α p`, a face other than the cell, are reached
from `p`. -/
theorem reach_across {x u w z : X.toCombMap.Dart} {J : ℕ} (hx : IsPocket X i x J)
    (hu : (X.toCombMap.facePerm ^ (J - 1)) x = u)
    (hw : (X.toCombMap.facePerm ^ ((cellDarts X i).length - 1)) x = w)
    (hface : X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x)) ≠
      (cell X i).face)
    (hz : X.toCombMap.faceOf (X.toCombMap.alpha z) =
      X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x))) :
    Reach X.toCombMap u w ((X.toCombMap.facePerm ^ J) x) z := by
  have hcellface : ∀ t : ℕ,
      X.toCombMap.faceOf ((X.toCombMap.facePerm ^ t) x) = (cell X i).face := fun t => by
    rw [faceOf_pow]
    exact faceOf_of_mem_cellDarts hx.1
  have h1 : Reach X.toCombMap u w ((X.toCombMap.facePerm ^ J) x)
      (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x)) :=
    Relation.EqvGen.rel _ _ (Or.inl rfl)
  have h2 : Reach X.toCombMap u w (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x))
      (X.toCombMap.alpha z) := by
    apply JunctionPocket.joined_reach_of_faceOf_eq
    · rw [← hu, hcellface]
      exact hface
    · rw [← hw, hcellface]
      exact hface
    · exact hz.symm
  have h3 : Reach X.toCombMap u w (X.toCombMap.alpha z) z :=
    Relation.EqvGen.rel _ _ (Or.inl (X.toCombMap.alpha_involutive z))
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ h1 h2) h3

/-- The index bookkeeping of a class arc `seg y l` through `p = f^J x`, with `y = f^a x` after the
pocket: either `y = p`, or the arc wraps around the cell and contains `d`. -/
theorem wrap_or_start {x y d : X.toCombMap.Dart} {J s a t l : ℕ} (hx : x ∈ cellDarts X i)
    (hs : s < J) (hd : (X.toCombMap.facePerm ^ s) x = d) (hJa : J ≤ a)
    (ha : a < (cellDarts X i).length) (hy : (X.toCombMap.facePerm ^ a) x = y)
    (ht : t < l) (hl : l ≤ (cellDarts X i).length)
    (hp : (X.toCombMap.facePerm ^ t) y = (X.toCombMap.facePerm ^ J) x) :
    (t = 0 ∧ a = J) ∨ (d ∈ seg X.toCombMap y l ∧ J < l) := by
  have h1 : (X.toCombMap.facePerm ^ (t + a)) x = (X.toCombMap.facePerm ^ J) x := by
    rw [pow_apply_add, hy, hp]
  by_cases hlt : t + a < (cellDarts X i).length
  · left
    have := pow_inj_cell hx hlt (by omega) h1
    exact ⟨by omega, by omega⟩
  · right
    have h2 : (X.toCombMap.facePerm ^ (t + a - (cellDarts X i).length)) x =
        (X.toCombMap.facePerm ^ J) x := by
      rw [← pow_add_length_cell hx (t + a - (cellDarts X i).length),
        Nat.sub_add_cancel (by omega : (cellDarts X i).length ≤ t + a)]
      exact h1
    have h3 := pow_inj_cell hx (by omega) (by omega) h2
    refine ⟨mem_seg_iff.mpr ⟨s + (cellDarts X i).length - a, by omega, ?_⟩, by omega⟩
    rw [← hy, ← pow_apply_add, show s + (cellDarts X i).length - a + a =
      s + (cellDarts X i).length by omega, pow_add_length_cell hx, hd]

end Separation

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.Reach
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.head?_seg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.sep_not_reach
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.not_reach_pow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.outside_index
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.reach_across
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.wrap_or_start
