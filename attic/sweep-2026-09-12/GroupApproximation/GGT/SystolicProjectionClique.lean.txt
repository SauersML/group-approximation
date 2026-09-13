import GroupApproximation.GGT.SystolicProjection
import GroupApproximation.GGT.SystolicBallDismantlable
import GroupApproximation.Meta.AxiomGuard

/-!
# Projection cliques in the one-skeleton of a 6-large triangle complex

Fix a base vertex `o` in the connected one-skeleton of a triangle complex with 6-large links,
and let `x`, `y` be distinct neighbours of `u`, each one step closer to `o` than `u`.  Then
`x` and `y` are adjacent.

The proof is by induction on `k = d(o, u)`.  Suppose `x` and `y` are not adjacent.  Walk from
`x` and from `y` one step at a time toward `o`.  The closed path `u, x, …, o, …, y, u` has
length `2k`.  Its vertices are distinct: the two descents cannot meet before `o`, since a
meeting vertex `o'` closer to `u` would make `x y` an edge by the induction hypothesis.  Least
discs then give the contradiction.  The two descents are geodesic arcs, each carrying curvature
at most one.  The corner `u` has degree at least three, and `o` has degree at least two.  The
total boundary curvature is therefore at most five, while `boundary_curvature_ge_six` requires
six.

* `stepToward hconn o w`: a neighbour of `w` one step closer to `o`.
* `sum_range_eq_split`: splitting a sum over `range n` at `0` and `k`.
* `projectionClique_of_linksSixLarge`: the projection clique condition.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic

open GGT.VanKampen TriangulatedDisc

universe u

/-- Splitting a sum over `range n` at the indices `0` and `k`. -/
theorem sum_range_eq_split (f : ℕ → ℤ) {k n : ℕ} (hk : 0 < k) (hkn : k < n) :
    ∑ i ∈ Finset.range n, f i =
      f 0 + ∑ i ∈ Finset.Ioo 0 k, f i + f k + ∑ i ∈ Finset.Ioo k n, f i := by
  have hsplit : Finset.range n = insert 0 (Finset.Ioo 0 k ∪ insert k (Finset.Ioo k n)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_union, Finset.mem_Ioo]
    omega
  have h0 : 0 ∉ Finset.Ioo 0 k ∪ insert k (Finset.Ioo k n) := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have := Finset.mem_Ioo.mp h
      omega
    · rcases Finset.mem_insert.mp h with h | h
      · omega
      · have := Finset.mem_Ioo.mp h
        omega
  have hk' : k ∉ Finset.Ioo k n := fun h => by
    have := Finset.mem_Ioo.mp h
    omega
  have hdisj : Disjoint (Finset.Ioo 0 k) (insert k (Finset.Ioo k n)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    have h1 := Finset.mem_Ioo.mp hi
    rcases Finset.mem_insert.mp hi' with h | h
    · omega
    · have := Finset.mem_Ioo.mp h
      omega
  rw [hsplit, Finset.sum_insert h0, Finset.sum_union hdisj, Finset.sum_insert hk']
  ring

section Step

variable {V : Type*} {G : SimpleGraph V}

/-- One step toward `o`: a neighbour of `w` one step closer to `o`, and `w` itself when
`w = o`. -/
noncomputable def stepToward (hconn : G.Connected) (o w : V) : V :=
  if h : 0 < G.dist o w then Classical.choose (BFS.exists_adj_predecessor hconn o h) else w

variable (hconn : G.Connected) {o : V}

theorem adj_stepToward {w : V} (hw : 0 < G.dist o w) : G.Adj w (stepToward hconn o w) := by
  unfold stepToward
  rw [dif_pos hw]
  exact (Classical.choose_spec (BFS.exists_adj_predecessor hconn o hw)).1

theorem dist_stepToward {w : V} (hw : 0 < G.dist o w) :
    G.dist o (stepToward hconn o w) + 1 = G.dist o w := by
  unfold stepToward
  rw [dif_pos hw]
  exact (Classical.choose_spec (BFS.exists_adj_predecessor hconn o hw)).2

theorem dist_iterate_stepToward {w : V} {i : ℕ} (hi : i ≤ G.dist o w) :
    G.dist o ((stepToward hconn o)^[i] w) + i = G.dist o w := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h := ih (by omega)
    have hpos : 0 < G.dist o ((stepToward hconn o)^[i] w) := by omega
    have h1 := dist_stepToward hconn hpos
    rw [Function.iterate_succ_apply']
    omega

theorem exists_walk_iterate_stepToward {w : V} {i : ℕ} (hi : i ≤ G.dist o w) :
    ∃ p : G.Walk w ((stepToward hconn o)^[i] w), p.length = i := by
  induction i with
  | zero => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ i ih =>
    obtain ⟨p, hp⟩ := ih (by omega)
    have h := dist_iterate_stepToward hconn (w := w) (i := i) (by omega)
    have hpos : 0 < G.dist o ((stepToward hconn o)^[i] w) := by omega
    rw [Function.iterate_succ_apply']
    exact ⟨p.concat (adj_stepToward hconn hpos), by rw [SimpleGraph.Walk.length_concat, hp]⟩

/-- `i` steps toward `o` from `w` travel distance exactly `i`. -/
theorem dist_iterate_stepToward_left {w : V} {i : ℕ} (hi : i ≤ G.dist o w) :
    G.dist ((stepToward hconn o)^[i] w) w = i := by
  obtain ⟨p, hp⟩ := exists_walk_iterate_stepToward hconn hi
  have h1 := SimpleGraph.dist_le p.reverse
  rw [SimpleGraph.Walk.length_reverse, hp] at h1
  have h2 := dist_iterate_stepToward hconn hi
  have h3 : G.dist o w ≤ G.dist o ((stepToward hconn o)^[i] w) +
      G.dist ((stepToward hconn o)^[i] w) w := hconn.dist_triangle
  omega

/-- `d(o, w)` steps toward `o` from `w` reach `o`. -/
theorem iterate_stepToward_dist {w : V} : (stepToward hconn o)^[G.dist o w] w = o := by
  have h := dist_iterate_stepToward hconn (w := w) (i := G.dist o w) le_rfl
  have h0 : G.dist o ((stepToward hconn o)^[G.dist o w] w) = 0 := by omega
  exact ((hconn.preconnected o _).dist_eq_zero_iff.mp h0).symm

end Step

variable {V : Type u} {X : TriangleComplex V}

/-- **Projection clique** in the one-skeleton of a simply connected triangle complex with
6-large links: the neighbours of `u` one step closer to `o` are pairwise adjacent.  Simple
connectivity enters through the filling statements `hfill` and `hfold`. -/
theorem projectionClique_of_linksSixLarge (hfill : FillingStatement X)
    (hfold : MirrorFoldStatement X) (h6 : LinksSixLarge X) (hconn : X.G.Connected) :
    ProjectionClique X.G := by
  suffices h : ∀ k : ℕ, ∀ o u x y : V, X.G.dist o u = k → X.G.Adj u x → X.G.Adj u y →
      X.G.dist o x + 1 = X.G.dist o u → X.G.dist o y + 1 = X.G.dist o u → x ≠ y →
        X.G.Adj x y by
    intro o u x y
    exact h _ o u x y rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro o u x y hk hux huy hx hy hne
    by_contra hxy
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hx0 : X.G.dist o x = 0 := by omega
      have hy0 : X.G.dist o y = 0 := by omega
      rw [(hconn.preconnected o x).dist_eq_zero_iff] at hx0
      rw [(hconn.preconnected o y).dist_eq_zero_iff] at hy0
      exact hne (hx0.symm.trans hy0)
    have hdx : X.G.dist o x = k - 1 := by omega
    have hdy : X.G.dist o y = k - 1 := by omega
    have hxo : (stepToward hconn o)^[k - 1] x = o := by
      have h := iterate_stepToward_dist hconn (o := o) (w := x)
      rwa [hdx] at h
    have hyo : (stepToward hconn o)^[k - 1] y = o := by
      have h := iterate_stepToward_dist hconn (o := o) (w := y)
      rwa [hdy] at h
    -- The closed path `u, x, …, o, …, y, u`.
    obtain ⟨g, hg0, hgx, hgy, hg2k⟩ : ∃ g : ℕ → V, g 0 = u ∧
        (∀ i, 0 < i → i ≤ k → g i = (stepToward hconn o)^[i - 1] x) ∧
        (∀ i, k ≤ i → i < 2 * k → g i = (stepToward hconn o)^[2 * k - 1 - i] y) ∧
        g (2 * k) = u := by
      refine ⟨fun i => if i = 0 then u else if i ≤ k then (stepToward hconn o)^[i - 1] x
        else if i < 2 * k then (stepToward hconn o)^[2 * k - 1 - i] y else u, if_pos rfl,
        fun i hi0 hik => (if_neg (show ¬ i = 0 by omega)).trans (if_pos hik),
        fun i hki hi2 => ?_,
        (if_neg (show ¬ 2 * k = 0 by omega)).trans
          ((if_neg (show ¬ 2 * k ≤ k by omega)).trans (if_neg (show ¬ 2 * k < 2 * k by omega)))⟩
      by_cases hik : i ≤ k
      · have hxy' : (stepToward hconn o)^[i - 1] x = (stepToward hconn o)^[2 * k - 1 - i] y := by
          rw [show i - 1 = k - 1 by omega, show 2 * k - 1 - i = k - 1 by omega, hxo, hyo]
        exact (if_neg (show ¬ i = 0 by omega)).trans ((if_pos hik).trans hxy')
      · exact (if_neg (show ¬ i = 0 by omega)).trans ((if_neg hik).trans (if_pos hi2))
    have hadj : ∀ i, i < 2 * k → X.G.Adj (g i) (g (i + 1)) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · show X.G.Adj (g 0) (g 1)
        rw [hg0, hgx 1 (by omega) (by omega)]
        exact hux
      · by_cases hik : i < k
        · have h1 := hgx i hi0 (by omega)
          have h2 := hgx (i + 1) (by omega) (by omega)
          rw [show i + 1 - 1 = i - 1 + 1 by omega, Function.iterate_succ_apply'] at h2
          have hd := dist_iterate_stepToward hconn (o := o) (w := x) (i := i - 1) (by omega)
          have hpos : 0 < X.G.dist o ((stepToward hconn o)^[i - 1] x) := by omega
          rw [h1, h2]
          exact adj_stepToward hconn hpos
        · have h1 := hgy i (by omega) hi
          by_cases hi2 : i + 1 < 2 * k
          · have h2 := hgy (i + 1) (by omega) hi2
            rw [show 2 * k - 1 - i = 2 * k - 1 - (i + 1) + 1 by omega,
              Function.iterate_succ_apply'] at h1
            have hd := dist_iterate_stepToward hconn (o := o) (w := y)
              (i := 2 * k - 1 - (i + 1)) (by omega)
            have hpos : 0 < X.G.dist o ((stepToward hconn o)^[2 * k - 1 - (i + 1)] y) := by
              omega
            rw [h1, h2]
            exact (adj_stepToward hconn hpos).symm
          · rw [h1, show i + 1 = 2 * k by omega, hg2k, show 2 * k - 1 - i = 0 by omega]
            exact huy.symm
    have hdlo : ∀ i, i ≤ k → X.G.dist o (g i) + i = k := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hg0]
        omega
      · rw [hgx i hi0 hi]
        have := dist_iterate_stepToward hconn (o := o) (w := x) (i := i - 1) (by omega)
        omega
    have hdhi : ∀ i, k ≤ i → i < 2 * k → X.G.dist o (g i) = i - k := by
      intro i hki hi2
      rw [hgy i hki hi2]
      have := dist_iterate_stepToward hconn (o := o) (w := y) (i := 2 * k - 1 - i) (by omega)
      omega
    -- The path runs through distinct vertices.
    have hne' : ∀ i j, i < j → j < 2 * k → g i ≠ g j := by
      intro i j hij hj heq
      by_cases hjk : j ≤ k
      · have h1 := hdlo i (by omega)
        have h2 := hdlo j hjk
        rw [heq] at h1
        omega
      · by_cases hik : k ≤ i
        · have h1 := hdhi i hik (by omega)
          have h2 := hdhi j (by omega) hj
          rw [heq] at h1
          omega
        · have h1 := hdlo i (by omega)
          have h2 := hdhi j (by omega) hj
          rw [heq] at h1
          have hi0 : 0 < i := by omega
          rw [hgx i hi0 (by omega), hgy j (by omega) hj,
            show 2 * k - 1 - j = i - 1 by omega] at heq
          have hmx : i - 1 ≤ X.G.dist o x := by omega
          have hmy : i - 1 ≤ X.G.dist o y := by omega
          have hdo := dist_iterate_stepToward hconn hmx
          have hox := dist_iterate_stepToward_left hconn hmx
          have hoy := dist_iterate_stepToward_left hconn hmy
          rw [← heq] at hoy
          have hou : X.G.dist ((stepToward hconn o)^[i - 1] x) u = i - 1 + 1 := by
            have h1' : X.G.dist ((stepToward hconn o)^[i - 1] x) u ≤
                X.G.dist ((stepToward hconn o)^[i - 1] x) x + X.G.dist x u :=
              hconn.dist_triangle
            have h2' : X.G.dist o u ≤ X.G.dist o ((stepToward hconn o)^[i - 1] x) +
                X.G.dist ((stepToward hconn o)^[i - 1] x) u := hconn.dist_triangle
            have h3' : X.G.dist x u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hux.symm
            omega
          exact hxy (ih (i - 1 + 1) (by omega) ((stepToward hconn o)^[i - 1] x) u x y hou hux
            huy (by omega) (by omega) hne)
    -- Least discs bound the curvature of the path.
    obtain ⟨γ, D, hint, hblen, hgD⟩ :=
      exists_disc_of_cycle hfill hfold h6 (n := 2 * k) (by omega) g (by rw [hg2k, hg0]) hadj
    have hS : D.SimpleBoundary := simpleBoundary_of_ne (by omega) hblen hgD hne'
    have hdeg0 : 3 ≤ D.bdeg 0 := by
      have hwrap : 2 * k - 1 + 1 = 0 + D.blen := by omega
      have h2 := hS.two_le_bdeg (2 * k - 1)
      rw [hwrap, D.bdeg_add_blen] at h2
      by_contra hlt
      have hadj' := hS.adj_of_bdeg_two (2 * k - 1) (by rw [hwrap, D.bdeg_add_blen]; omega)
      rw [show 2 * k - 1 + 2 = 1 + D.blen by omega, D.bvert_add_blen, hgD 1 (by omega),
        hgD (2 * k - 1) (by omega), hgy (2 * k - 1) (by omega) (by omega),
        show 2 * k - 1 - (2 * k - 1) = 0 by omega, hgx 1 (by omega) (by omega)] at hadj'
      exact hxy hadj'.symm
    have hdegk := hS.two_le_bdeg (k - 1)
    rw [show k - 1 + 1 = k by omega] at hdegk
    have hs1 := hS.side_le_one (a := 0) (b := k) (by omega) (by
      rw [hgD 0 (by omega), hgD k (by omega), hg0, hgx k (by omega) le_rfl, hxo,
        SimpleGraph.dist_comm]
      omega)
    have hs2 := hS.side_le_one (a := k) (b := 2 * k) (by omega) (by
      rw [hgD k (by omega), hgD (2 * k) le_rfl, hgx k (by omega) le_rfl, hxo, hg2k]
      omega)
    have hsum := hS.boundary_curvature_ge_six hint
    rw [hblen, sum_range_eq_split (fun i => (4 : ℤ) - D.bdeg i) (by omega : 0 < k)
      (by omega : k < 2 * k)] at hsum
    omega

end Systolic
end GroupApproximation

open GroupApproximation.Systolic

#audit_axioms sum_range_eq_split
#audit_axioms adj_stepToward
#audit_axioms dist_stepToward
#audit_axioms dist_iterate_stepToward
#audit_axioms exists_walk_iterate_stepToward
#audit_axioms dist_iterate_stepToward_left
#audit_axioms iterate_stepToward_dist
#audit_axioms projectionClique_of_linksSixLarge
