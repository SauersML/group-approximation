import GroupApproximation.GroupTheory.TreeGraphGeometry

/-!
# The metric space of a tree, and its `0`-hyperbolicity

`GroupTheory/TreeGraphGeometry.lean` proves the combinatorial core of tree
geometry: unique geodesics, the additive splitting of graph distance along
them, and Gromov's four-point inequality with one unit of slack.  This module
removes the slack and packages the result as a `PseudoMetricSpace`, so that the
vocabulary of `Sofic/HullSuitabilityGeometry.lean` --- `IsHyperbolicSpace`,
`IsLoxodromic`, `Independent`, `IsAcylindrical` --- applies to a tree verbatim.

## Where the slack came from, and why it is not there

`TreeGraphGeometry.graphDist_fourPoint_one` chooses the branch point at depth
`⌊min A B / 2⌋` on the geodesic from the basepoint, where `A` and `B` are the
two doubled Gromov products, and the estimate then loses whatever `min A B`
carried in its last bit.  That bit is always zero, because in a tree every
doubled Gromov product is even.  The three steps are:

* `dist_ne_of_adj` --- adjacent vertices of a tree are at *different* distances
  from any root.  If they were equal, then either the geodesic from one of them
  to the root already passes through the other, and the additive splitting
  `dist_add_dist_eq_of_mem_geodesic` reads `n + 1 = n`; or it does not, and
  prefixing it by the edge produces a second path to the root, which
  unique-path-ness identifies with the geodesic, and the lengths read
  `n + 1 = n` again.  This is the only place where acyclicity is used directly.
* `dist_parity` --- so distance from a root flips parity across every edge, and
  an induction along an arbitrary walk gives that `d(r,x) + d(r,y) + ℓ(p)` is
  even for every walk `p` from `x` to `y`.  Taking `p` to be the geodesic:
  `d(r,x) + d(r,y) + d(x,y)` is even, i.e. every Gromov product of a tree is an
  integer.
* `graphDist_fourPoint_zero` --- with `min A B` even the branch point sits at
  depth exactly `min A B / 2`, and the estimate of `TreeGraphGeometry` closes
  with nothing to spare.

## The space

`TreeSpace hH` is the vertex set carrying the real-valued graph metric.  It is
a type synonym indexed by the *proof* that the graph is a tree, for two
reasons: the vertex type may carry a metric of its own, and connectedness --- a
consequence of the tree hypothesis, not of the graph alone --- is what makes
the triangle inequality true, so the instance genuinely depends on `hH`.

`isHyperbolicSpace_zero` is then Gromov's four-point condition at `δ = 0`, in
the exact form `HullGeometry.IsHyperbolicSpace` states it.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.TreeGraphGeometry

universe u

section Tree

variable {V : Type u} (H : SimpleGraph V)

/-! ## Prefixing a path by an edge -/

/-- Prefixing a path by an edge to a vertex outside it is again a path.  This
is stated here because the parity argument needs the *strict* growth of path
length across one edge, which `SimpleGraph.dist_le` does not provide. -/
theorem isPath_cons {u v w : V} (h : H.Adj u v) {p : H.Walk v w}
    (hp : p.IsPath) (hu : u ∉ p.support) :
    (SimpleGraph.Walk.cons h p).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons,
    List.nodup_cons]
  exact ⟨hu, SimpleGraph.Walk.isPath_def.mp hp⟩

/-! ## Parity of the graph metric of a tree -/

variable (hH : H.IsTree)

/-- **Adjacent vertices of a tree are at different distances from any root.**
The two cases are whether the geodesic from `v` to the root already meets `u`.
-/
theorem dist_ne_of_adj (hH : H.IsTree) (r : V) {u v : V} (huv : H.Adj u v) :
    H.dist r u ≠ H.dist r v := by
  classical
  intro heq
  have hvu : H.dist v u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv.symm
  have hcru : H.dist r u = H.dist u r := SimpleGraph.dist_comm
  have hcrv : H.dist r v = H.dist v r := SimpleGraph.dist_comm
  by_cases hu : u ∈ (geodesic H hH v r).support
  · have hsplit : H.dist v u + H.dist u r = H.dist v r :=
      dist_add_dist_eq_of_mem_geodesic H hH hu
    omega
  · have hp : (SimpleGraph.Walk.cons huv (geodesic H hH v r)).IsPath :=
      isPath_cons H huv (geodesic_isPath H hH v r) hu
    have heqp : SimpleGraph.Walk.cons huv (geodesic H hH v r)
        = geodesic H hH u r :=
      congrArg Subtype.val
        (hH.isAcyclic.path_unique ⟨_, hp⟩
          ⟨geodesic H hH u r, geodesic_isPath H hH u r⟩)
    have hlen : (SimpleGraph.Walk.cons huv (geodesic H hH v r)).length
        = H.dist u r := by
      rw [heqp]
      exact geodesic_length H hH u r
    rw [SimpleGraph.Walk.length_cons, geodesic_length] at hlen
    omega

/-- **Distance from a root flips parity across every edge**, so along a walk it
changes by the length of the walk, modulo two. -/
theorem dist_add_dist_add_length_even (hH : H.IsTree) (r : V) {x y : V} (p : H.Walk x y) :
    (H.dist r x + H.dist r y + p.length) % 2 = 0 := by
  induction p with
  | nil =>
    simp only [SimpleGraph.Walk.length_nil]
    omega
  | @cons a b c hab q ih =>
    have hne : H.dist r a ≠ H.dist r b := dist_ne_of_adj H hH r hab
    have hab1 : H.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab
    have hba : H.dist b a = H.dist a b := SimpleGraph.dist_comm
    have h1 := hH.connected.dist_triangle (u := r) (v := b) (w := a)
    have h2 := hH.connected.dist_triangle (u := r) (v := a) (w := b)
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- **Every Gromov product of a tree is an integer**: the doubled product
`d(r,x) + d(r,y) - d(x,y)` is even. -/
theorem dist_parity (hH : H.IsTree) (r x y : V) :
    (H.dist r x + H.dist r y + H.dist x y) % 2 = 0 := by
  have h := dist_add_dist_add_length_even H hH r (geodesic H hH x y)
  rwa [geodesic_length] at h

/-! ## The sharp four-point inequality -/

/-- **The four-point inequality for a tree, with no slack.**  This is
`TreeGraphGeometry.graphDist_fourPoint_one` run at the exact half of `min A B`,
which `dist_parity` makes an integer. -/
theorem graphDist_fourPoint_zero (hH : H.IsTree) (w x y z : V) :
    min (H.dist x w + H.dist y w - H.dist x y)
        (H.dist y w + H.dist z w - H.dist y z) ≤
      H.dist x w + H.dist z w - H.dist x z := by
  classical
  have hcx : H.dist w x = H.dist x w := SimpleGraph.dist_comm
  have hcy : H.dist w y = H.dist y w := SimpleGraph.dist_comm
  have hcz : H.dist w z = H.dist z w := SimpleGraph.dist_comm
  have hzy : H.dist z y = H.dist y z := SimpleGraph.dist_comm
  have hpxy := dist_parity H hH w x y
  have hpyz := dist_parity H hH w y z
  have hxyTri : H.dist x y ≤ H.dist x w + H.dist y w := by
    have h := hH.connected.dist_triangle (u := x) (v := w) (w := y)
    omega
  have hyzTri : H.dist y z ≤ H.dist y w + H.dist z w := by
    have h := hH.connected.dist_triangle (u := y) (v := w) (w := z)
    omega
  have hxwTri : H.dist x w ≤ H.dist x y + H.dist y w := by
    have h := hH.connected.dist_triangle (u := x) (v := y) (w := w)
    omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * k =
      min (H.dist x w + H.dist y w - H.dist x y)
        (H.dist y w + H.dist z w - H.dist y z) :=
    ⟨min (H.dist x w + H.dist y w - H.dist x y)
        (H.dist y w + H.dist z w - H.dist y z) / 2, by omega⟩
  have hkY : k ≤ H.dist w y := by omega
  have hkxy : 2 * k + H.dist x y ≤ H.dist x w + H.dist y w := by omega
  have hkzy : 2 * k + H.dist z y ≤ H.dist z w + H.dist y w := by omega
  have hvx : (geodesic H hH w y).getVert k ∈ (geodesic H hH w x).support :=
    getVert_mem_of_two_mul_le_overlap H hH hkY hkxy
  have hvz : (geodesic H hH w y).getVert k ∈ (geodesic H hH w z).support :=
    getVert_mem_of_two_mul_le_overlap H hH hkY hkzy
  have hwv : H.dist w ((geodesic H hH w y).getVert k) = k :=
    dist_getVert_geodesic H hH hkY
  have hsx : H.dist w ((geodesic H hH w y).getVert k)
      + H.dist ((geodesic H hH w y).getVert k) x = H.dist w x :=
    dist_add_dist_eq_of_mem_geodesic H hH hvx
  have hsz : H.dist w ((geodesic H hH w y).getVert k)
      + H.dist ((geodesic H hH w y).getVert k) z = H.dist w z :=
    dist_add_dist_eq_of_mem_geodesic H hH hvz
  have hxzV := hH.connected.dist_triangle (u := x)
      (v := (geodesic H hH w y).getVert k) (w := z)
  have hxv : H.dist x ((geodesic H hH w y).getVert k)
      = H.dist ((geodesic H hH w y).getVert k) x := SimpleGraph.dist_comm
  omega

/-- The four-point inequality of a tree, cast to `ℝ` and divided by two: this
is Gromov's condition on the products themselves, at `δ = 0`. -/
theorem gromovProduct_fourPoint_zero_real (hH : H.IsTree) (w x y z : V) :
    min (((H.dist x w : ℝ) + H.dist y w - H.dist x y) / 2)
        (((H.dist y w : ℝ) + H.dist z w - H.dist y z) / 2)
      ≤ ((H.dist x w : ℝ) + H.dist z w - H.dist x z) / 2 := by
  have key := graphDist_fourPoint_zero H hH w x y z
  have hxyTri : H.dist x y ≤ H.dist x w + H.dist y w := by
    have h := hH.connected.dist_triangle (u := x) (v := w) (w := y)
    have hc : H.dist w y = H.dist y w := SimpleGraph.dist_comm
    omega
  have hyzTri : H.dist y z ≤ H.dist y w + H.dist z w := by
    have h := hH.connected.dist_triangle (u := y) (v := w) (w := z)
    have hc : H.dist w z = H.dist z w := SimpleGraph.dist_comm
    omega
  have hxzTri : H.dist x z ≤ H.dist x w + H.dist z w := by
    have h := hH.connected.dist_triangle (u := x) (v := w) (w := z)
    have hc : H.dist w z = H.dist z w := SimpleGraph.dist_comm
    omega
  rcases le_total (H.dist x w + H.dist y w - H.dist x y)
      (H.dist y w + H.dist z w - H.dist y z) with hle | hle
  · have hnat : H.dist x w + H.dist y w + H.dist x z
        ≤ H.dist x w + H.dist z w + H.dist x y := by omega
    have hreal : (H.dist x w : ℝ) + H.dist y w + H.dist x z
        ≤ (H.dist x w : ℝ) + H.dist z w + H.dist x y := by exact_mod_cast hnat
    have hm := min_le_left (((H.dist x w : ℝ) + H.dist y w - H.dist x y) / 2)
      (((H.dist y w : ℝ) + H.dist z w - H.dist y z) / 2)
    linarith
  · have hnat : H.dist y w + H.dist z w + H.dist x z
        ≤ H.dist x w + H.dist z w + H.dist y z := by omega
    have hreal : (H.dist y w : ℝ) + H.dist z w + H.dist x z
        ≤ (H.dist x w : ℝ) + H.dist z w + H.dist y z := by exact_mod_cast hnat
    have hm := min_le_right (((H.dist x w : ℝ) + H.dist y w - H.dist x y) / 2)
      (((H.dist y w : ℝ) + H.dist z w - H.dist y z) / 2)
    linarith

end Tree

/-! ## The tree as a metric space -/

/-- **The vertex set of a tree as a metric space.**  A type synonym indexed by
the tree hypothesis: the vertex type may already carry a metric, and the
triangle inequality for the graph metric needs connectedness, which is part of
`hH` and not of `H`. -/
def TreeSpace {V : Type u} {H : SimpleGraph V} (_hH : H.IsTree) : Type u := V

/-- The point of `TreeSpace hH` named by a vertex. -/
def TreeSpace.of {V : Type u} {H : SimpleGraph V} (hH : H.IsTree) (v : V) :
    TreeSpace hH := v

/-- The vertex naming a point of `TreeSpace hH`. -/
def TreeSpace.val {V : Type u} {H : SimpleGraph V} {hH : H.IsTree}
    (x : TreeSpace hH) : V := x

@[simp] theorem TreeSpace.val_of {V : Type u} {H : SimpleGraph V}
    (hH : H.IsTree) (v : V) : TreeSpace.val (TreeSpace.of hH v) = v := rfl

@[simp] theorem TreeSpace.of_val {V : Type u} {H : SimpleGraph V}
    {hH : H.IsTree} (x : TreeSpace hH) :
    TreeSpace.of hH (TreeSpace.val x) = x := rfl

/-- The graph metric, cast to `ℝ`.  Symmetry and the triangle inequality are
`SimpleGraph.dist_comm` and `SimpleGraph.Connected.dist_triangle`; the latter is
where the tree hypothesis enters. -/
noncomputable instance instPseudoMetricSpaceTreeSpace {V : Type u}
    {H : SimpleGraph V} (hH : H.IsTree) : PseudoMetricSpace (TreeSpace hH) where
  dist x y := (H.dist (TreeSpace.val x) (TreeSpace.val y) : ℝ)
  dist_self x := by
    show ((H.dist (TreeSpace.val x) (TreeSpace.val x) : ℕ) : ℝ) = 0
    simp
  dist_comm x y := by
    show ((H.dist (TreeSpace.val x) (TreeSpace.val y) : ℕ) : ℝ)
      = ((H.dist (TreeSpace.val y) (TreeSpace.val x) : ℕ) : ℝ)
    rw [SimpleGraph.dist_comm]
  dist_triangle x y z := by
    show ((H.dist (TreeSpace.val x) (TreeSpace.val z) : ℕ) : ℝ)
      ≤ ((H.dist (TreeSpace.val x) (TreeSpace.val y) : ℕ) : ℝ)
        + ((H.dist (TreeSpace.val y) (TreeSpace.val z) : ℕ) : ℝ)
    exact_mod_cast hH.connected.dist_triangle (u := TreeSpace.val x)
      (v := TreeSpace.val y) (w := TreeSpace.val z)

@[simp] theorem TreeSpace.dist_eq {V : Type u} {H : SimpleGraph V}
    {hH : H.IsTree} (x y : TreeSpace hH) :
    dist x y = (H.dist (TreeSpace.val x) (TreeSpace.val y) : ℝ) := rfl

@[simp] theorem TreeSpace.dist_of {V : Type u} {H : SimpleGraph V}
    {hH : H.IsTree} (u v : V) :
    dist (TreeSpace.of hH u) (TreeSpace.of hH v) = (H.dist u v : ℝ) := rfl

/-- **A tree is `0`-hyperbolic.**  The first `IsHyperbolicSpace` witness in the
library that is neither bounded nor a line. -/
theorem isHyperbolicSpace_zero {V : Type u} {H : SimpleGraph V}
    (hH : H.IsTree) : IsHyperbolicSpace 0 (TreeSpace hH) := by
  intro w x y z
  have h := gromovProduct_fourPoint_zero_real H hH (TreeSpace.val w)
    (TreeSpace.val x) (TreeSpace.val y) (TreeSpace.val z)
  simp only [gromovProduct, TreeSpace.dist_eq]
  linarith

end GGT
end GroupApproximation
