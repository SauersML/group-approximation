import GroupApproximation.GGT.SystolicProjectionClique
import GroupApproximation.Meta.AxiomGuard

/-!
# The triangle condition in the one-skeleton of a 6-large triangle complex

Fix a base vertex `o` in the connected one-skeleton of a simply connected triangle complex with
6-large links.  Let `u v` be an edge whose endpoints both lie at distance `j > 0` from `o`.  Then
`u` and `v` have a common neighbour at distance `j - 1` from `o`.

The proof is by strong induction on `j`.  Suppose there is no such neighbour; then `j ≥ 2`.  Walk
from `u` and from `v` one step at a time toward `o`, reaching `o` after `j` steps.  The closed
path `u, …, o, …, v, u` has length `2 j + 1`.  Its vertices are distinct.  A vertex `w` on both
descents lies at the same distance `a < j` from `u` and from `v`.  The induction hypothesis at `w`
then gives a common neighbour at distance `a - 1` from `w`, so at distance `j - 1` from `o`.

Least discs then bound the boundary curvature.
* The two descents are geodesic arcs, each carrying curvature at most one.
* The corners `u` and `v` have degree at least three.  A corner of degree two makes its boundary
  neighbours adjacent, and the first step of the other descent is then a common neighbour.
* The corner `o` has degree at least three.  Otherwise the vertices `a`, `b` before `o` on the two
  descents are adjacent, and `d(a, v)` is `j - 1` or `j`.  If it is `j - 1`, the induction
  hypothesis at `a` gives a common neighbour.  If it is `j`, then `u` and the first step `c` of the
  descent from `v` are neighbours of `v` one step closer to `a`.  The projection clique makes
  `u c` an edge, and `c` is a common neighbour.
So the total boundary curvature is at most five, while `boundary_curvature_ge_six` requires six.

* `sum_range_succ_eq_split`: splitting a sum over `range (m + 1)` at `0`, `k` and `m`.
* `triangleCondition_of_linksSixLarge`: the triangle condition.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic

open GGT.VanKampen TriangulatedDisc

universe u

/-- Splitting a sum over `range (m + 1)` at the indices `0`, `k` and `m`. -/
theorem sum_range_succ_eq_split (f : ℕ → ℤ) {k m : ℕ} (hk : 0 < k) (hkm : k < m) :
    ∑ i ∈ Finset.range (m + 1), f i =
      f 0 + ∑ i ∈ Finset.Ioo 0 k, f i + f k + ∑ i ∈ Finset.Ioo k m, f i + f m := by
  rw [sum_range_eq_split f hk (by omega : k < m + 1)]
  have hsplit : Finset.Ioo k (m + 1) = insert m (Finset.Ioo k m) := by
    ext i
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  have hm : m ∉ Finset.Ioo k m := fun h => by
    have := Finset.mem_Ioo.mp h
    omega
  rw [hsplit, Finset.sum_insert hm]
  ring

variable {V : Type u} {X : TriangleComplex V}

/-- **Triangle condition** in the one-skeleton of a simply connected triangle complex with
6-large links: two adjacent vertices at the same positive distance from `o` have a common
neighbour one step closer to `o`.  Simple connectivity enters through the filling statements
`hfill` and `hfold`. -/
theorem triangleCondition_of_linksSixLarge (hfill : FillingStatement X)
    (hfold : MirrorFoldStatement X) (h6 : LinksSixLarge X) (hconn : X.G.Connected) :
    TriangleCondition X.G := by
  have hPC := projectionClique_of_linksSixLarge hfill hfold h6 hconn
  suffices h : ∀ j : ℕ, ∀ o u v : V, X.G.Adj u v → X.G.dist o u = j → X.G.dist o v = j →
      0 < j → ∃ c : V, X.G.Adj u c ∧ X.G.Adj v c ∧ X.G.dist o c + 1 = j by
    intro o u v huv hdist hpos
    exact h _ o u v huv rfl hdist.symm hpos
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro o u v huv hu hv hj
    by_contra hno
    -- A common neighbour of `u` and `v` within distance `j - 1` of `o` is a witness.
    have hwit : ∀ c, X.G.Adj u c → X.G.Adj v c → X.G.dist o c + 1 ≤ j → False := by
      intro c huc hvc hc
      have := BFS.adjDist_le_succ hconn o huc
      exact hno ⟨c, huc, hvc, by omega⟩
    have hj2 : 2 ≤ j := by
      by_contra hlt
      have hj1 : j = 1 := by omega
      have hou : X.G.Adj o u := SimpleGraph.dist_eq_one_iff_adj.mp (hu.trans hj1)
      have hov : X.G.Adj o v := SimpleGraph.dist_eq_one_iff_adj.mp (hv.trans hj1)
      exact hwit o hou.symm hov.symm (by rw [SimpleGraph.dist_self]; omega)
    have huo : (stepToward hconn o)^[j] u = o := by
      have h := iterate_stepToward_dist hconn (o := o) (w := u)
      rwa [hu] at h
    have hvo : (stepToward hconn o)^[j] v = o := by
      have h := iterate_stepToward_dist hconn (o := o) (w := v)
      rwa [hv] at h
    -- The closed path `u, …, o, …, v, u`.
    obtain ⟨g, hgP, hgQ, hgn⟩ : ∃ g : ℕ → V,
        (∀ i, i ≤ j → g i = (stepToward hconn o)^[i] u) ∧
        (∀ i, j ≤ i → i ≤ 2 * j → g i = (stepToward hconn o)^[2 * j - i] v) ∧
        g (2 * j + 1) = u := by
      refine ⟨fun i => if i ≤ j then (stepToward hconn o)^[i] u
        else if i ≤ 2 * j then (stepToward hconn o)^[2 * j - i] v else u,
        fun i hi => if_pos hi, fun i hji hi2 => ?_,
        (if_neg (show ¬ 2 * j + 1 ≤ j by omega)).trans
          (if_neg (show ¬ 2 * j + 1 ≤ 2 * j by omega))⟩
      by_cases hij : i ≤ j
      · refine (if_pos hij).trans ?_
        rw [show i = j by omega, show 2 * j - j = j by omega, huo, hvo]
      · exact (if_neg hij).trans (if_pos hi2)
    have hadj : ∀ i, i < 2 * j + 1 → X.G.Adj (g i) (g (i + 1)) := by
      intro i hi
      by_cases hij : i < j
      · have hd := dist_iterate_stepToward hconn (o := o) (w := u) (i := i) (by omega)
        rw [hgP i (by omega), hgP (i + 1) (by omega), Function.iterate_succ_apply']
        exact adj_stepToward hconn (by omega)
      · by_cases hi2 : i < 2 * j
        · have hd := dist_iterate_stepToward hconn (o := o) (w := v) (i := 2 * j - (i + 1))
            (by omega)
          rw [hgQ i (by omega) (by omega), hgQ (i + 1) (by omega) (by omega),
            show 2 * j - i = 2 * j - (i + 1) + 1 by omega, Function.iterate_succ_apply']
          exact (adj_stepToward hconn (by omega)).symm
        · have hgi : g i = (stepToward hconn o)^[2 * j - i] v := hgQ i (by omega) (by omega)
          rw [hgi, show 2 * j - i = 0 by omega, show i + 1 = 2 * j + 1 by omega, hgn]
          exact huv.symm
    have hdP : ∀ i, i ≤ j → X.G.dist o (g i) + i = j := by
      intro i hi
      have := dist_iterate_stepToward hconn (o := o) (w := u) (i := i) (by omega)
      rw [hgP i hi]
      omega
    have hdQ : ∀ i, j ≤ i → i ≤ 2 * j → X.G.dist o (g i) + j = i := by
      intro i hji hi2
      have := dist_iterate_stepToward hconn (o := o) (w := v) (i := 2 * j - i) (by omega)
      rw [hgQ i hji hi2]
      omega
    -- The path runs through distinct vertices.
    have hne' : ∀ a b, a < b → b < 2 * j + 1 → g a ≠ g b := by
      intro a b hab hb heq
      by_cases hbj : b ≤ j
      · have h1 := hdP a (by omega)
        have h2 := hdP b hbj
        rw [heq] at h1
        omega
      · by_cases haj : j ≤ a
        · have h1 := hdQ a haj (by omega)
          have h2 := hdQ b (by omega) (by omega)
          rw [heq] at h1
          omega
        · have h1 := hdP a (by omega)
          have h2 := hdQ b (by omega) (by omega)
          rw [heq] at h1
          rw [hgP a (by omega), hgQ b (by omega) (by omega), show 2 * j - b = a by omega] at heq
          rcases Nat.eq_zero_or_pos a with rfl | ha0
          · exact huv.ne heq
          · have hau := dist_iterate_stepToward_left hconn (o := o) (w := u) (i := a) (by omega)
            have hav := dist_iterate_stepToward_left hconn (o := o) (w := v) (i := a) (by omega)
            have hoa := dist_iterate_stepToward hconn (o := o) (w := u) (i := a) (by omega)
            rw [← heq] at hav
            obtain ⟨c, huc, hvc, hc⟩ := ih a (by omega) _ u v huv hau hav ha0
            have htri : X.G.dist o c ≤ X.G.dist o ((stepToward hconn o)^[a] u) +
                X.G.dist ((stepToward hconn o)^[a] u) c := hconn.dist_triangle
            exact hwit c huc hvc (by omega)
    have hg0 : g 0 = u := hgP 0 (Nat.zero_le _)
    have hgj : g j = o := (hgP j le_rfl).trans huo
    have hg2j : g (2 * j) = v := by
      have h := hgQ (2 * j) (by omega) le_rfl
      rw [Nat.sub_self] at h
      exact h
    have hg1 : g 1 = stepToward hconn o u := hgP 1 (by omega)
    have hg2j1 : g (2 * j - 1) = stepToward hconn o v := by
      have h := hgQ (2 * j - 1) (by omega) (by omega)
      rw [show 2 * j - (2 * j - 1) = 1 by omega] at h
      exact h
    -- Least discs bound the curvature of the path.
    obtain ⟨γ, D, hint, hblen, hgD⟩ :=
      exists_disc_of_cycle hfill hfold h6 (n := 2 * j + 1) (by omega) g (by rw [hgn, hg0]) hadj
    have hS : D.SimpleBoundary := simpleBoundary_of_ne (by omega) hblen hgD hne'
    -- The corner `u`.
    have hdeg0 : 3 ≤ D.bdeg 0 := by
      have hwrap : 2 * j + 1 = 0 + D.blen := by omega
      have h2 := hS.two_le_bdeg (2 * j)
      rw [hwrap, D.bdeg_add_blen] at h2
      by_contra hlt
      have hadj' := hS.adj_of_bdeg_two (2 * j) (by rw [hwrap, D.bdeg_add_blen]; omega)
      rw [show 2 * j + 2 = 1 + D.blen by omega, D.bvert_add_blen, hgD 1 (by omega),
        hgD (2 * j) (by omega), hg1, hg2j] at hadj'
      have hpos : 0 < X.G.dist o u := by omega
      have hd := dist_stepToward hconn hpos
      exact hwit _ (adj_stepToward hconn hpos) hadj' (by omega)
    -- The corner `v`.
    have hdeg2j : 3 ≤ D.bdeg (2 * j) := by
      have h2 := hS.two_le_bdeg (2 * j - 1)
      rw [show 2 * j - 1 + 1 = 2 * j by omega] at h2
      by_contra hlt
      have hadj' := hS.adj_of_bdeg_two (2 * j - 1)
        (by rw [show 2 * j - 1 + 1 = 2 * j by omega]; omega)
      rw [show 2 * j - 1 + 2 = 2 * j + 1 by omega, hgD (2 * j - 1) (by omega),
        hgD (2 * j + 1) le_rfl, hg2j1, hgn] at hadj'
      have hpos : 0 < X.G.dist o v := by omega
      have hd := dist_stepToward hconn hpos
      exact hwit _ hadj'.symm (adj_stepToward hconn hpos) (by omega)
    -- The corner `o`.
    have hdegj : 3 ≤ D.bdeg j := by
      have h2 := hS.two_le_bdeg (j - 1)
      rw [show j - 1 + 1 = j by omega] at h2
      by_contra hlt
      have hadj' := hS.adj_of_bdeg_two (j - 1) (by rw [show j - 1 + 1 = j by omega]; omega)
      have hgb : g (j + 1) = (stepToward hconn o)^[j - 1] v := by
        have h := hgQ (j + 1) (by omega) (by omega)
        rw [show 2 * j - (j + 1) = j - 1 by omega] at h
        exact h
      rw [show j - 1 + 2 = j + 1 by omega, hgD (j - 1) (by omega), hgD (j + 1) (by omega),
        hgP (j - 1) (by omega), hgb] at hadj'
      -- `a = (stepToward hconn o)^[j - 1] u` and `b = (stepToward hconn o)^[j - 1] v` are adjacent.
      have hau := dist_iterate_stepToward_left hconn (o := o) (w := u) (i := j - 1) (by omega)
      have hoa := dist_iterate_stepToward hconn (o := o) (w := u) (i := j - 1) (by omega)
      have hbv := dist_iterate_stepToward_left hconn (o := o) (w := v) (i := j - 1) (by omega)
      have hab := SimpleGraph.dist_eq_one_iff_adj.mpr hadj'
      have htr1 : X.G.dist ((stepToward hconn o)^[j - 1] u) v ≤
          X.G.dist ((stepToward hconn o)^[j - 1] u) ((stepToward hconn o)^[j - 1] v) +
            X.G.dist ((stepToward hconn o)^[j - 1] v) v := hconn.dist_triangle
      have htr2 : X.G.dist o v ≤ X.G.dist o ((stepToward hconn o)^[j - 1] u) +
          X.G.dist ((stepToward hconn o)^[j - 1] u) v := hconn.dist_triangle
      by_cases hav : X.G.dist ((stepToward hconn o)^[j - 1] u) v = j - 1
      · obtain ⟨c, huc, hvc, hc⟩ := ih (j - 1) (by omega) _ u v huv hau hav (by omega)
        have htr3 : X.G.dist o c ≤ X.G.dist o ((stepToward hconn o)^[j - 1] u) +
            X.G.dist ((stepToward hconn o)^[j - 1] u) c := hconn.dist_triangle
        exact hwit c huc hvc (by omega)
      · have hpos : 0 < X.G.dist o v := by omega
        have hvc := adj_stepToward hconn hpos
        have hdc := dist_stepToward hconn hpos
        have hbc : X.G.dist ((stepToward hconn o)^[j - 1] v) (stepToward hconn o v) = j - 2 := by
          have h := dist_iterate_stepToward_left hconn (o := o) (w := stepToward hconn o v)
            (i := j - 2) (by omega)
          rw [show j - 1 = j - 2 + 1 by omega, Function.iterate_succ_apply]
          exact h
        have htr4 : X.G.dist ((stepToward hconn o)^[j - 1] u) (stepToward hconn o v) ≤
            X.G.dist ((stepToward hconn o)^[j - 1] u) ((stepToward hconn o)^[j - 1] v) +
              X.G.dist ((stepToward hconn o)^[j - 1] v) (stepToward hconn o v) :=
          hconn.dist_triangle
        have htr5 := BFS.adjDist_le_succ hconn ((stepToward hconn o)^[j - 1] u) hvc
        have huc := hPC ((stepToward hconn o)^[j - 1] u) v u (stepToward hconn o v) huv.symm hvc
          (by omega) (by omega) (fun h => by rw [← h] at hdc; omega)
        exact hwit _ huc hvc (by omega)
    -- The two descents.
    have hs1 := hS.side_le_one (a := 0) (b := j) (by omega) (by
      rw [hgD 0 (by omega), hgD j (by omega), hg0, hgj, SimpleGraph.dist_comm]
      omega)
    have hs2 := hS.side_le_one (a := j) (b := 2 * j) (by omega) (by
      rw [hgD j (by omega), hgD (2 * j) (by omega), hgj, hg2j]
      omega)
    have hsum := hS.boundary_curvature_ge_six hint
    rw [hblen, sum_range_succ_eq_split (fun i => (4 : ℤ) - D.bdeg i) (by omega : 0 < j)
      (by omega : j < 2 * j)] at hsum
    omega

end Systolic
end GroupApproximation

open GroupApproximation.Systolic

#audit_axioms sum_range_succ_eq_split
#audit_axioms triangleCondition_of_linksSixLarge
