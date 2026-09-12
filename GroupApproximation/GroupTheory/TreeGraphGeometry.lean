import GroupApproximation.Sofic.HullSuitabilityGeometry
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Geodesic triangles in a combinatorial tree

This module isolates the graph-theoretic core of the Bass--Serre
hyperbolicity proof.  In a connected acyclic graph, the unique simple path
between two vertices is the bypass of any walk between them.  Consequently
every vertex on one side of a geodesic triangle lies on one of the other two
sides.  This is the exact zero-thinness statement from which the Gromov
four-point inequality for the real-cast graph metric is derived.
-/

namespace GroupApproximation
namespace TreeGraphGeometry

universe u

variable {V : Type u} (H : SimpleGraph V) (hH : H.IsTree)

/-- The unique simple path between two vertices of a tree. -/
noncomputable def geodesic (x y : V) : H.Walk x y :=
  Classical.choose (hH.connected.exists_path_of_dist x y)

theorem geodesic_isPath (x y : V) : (geodesic H hH x y).IsPath :=
  (Classical.choose_spec (hH.connected.exists_path_of_dist x y)).1

@[simp] theorem geodesic_length (x y : V) :
    (geodesic H hH x y).length = H.dist x y :=
  (Classical.choose_spec (hH.connected.exists_path_of_dist x y)).2

/-- **Tree triangles are zero-thin, combinatorially.**  Every vertex of the
`w--y` geodesic lies on the `w--x` geodesic or on the `x--y` geodesic. -/
theorem mem_geodesic_left_or_right {w x y z : V}
    (hz : z ∈ (geodesic H hH w y).support) :
    z ∈ (geodesic H hH w x).support ∨
      z ∈ (geodesic H hH x y).support := by
  classical
  let p := geodesic H hH w x
  let q := geodesic H hH x y
  let r := geodesic H hH w y
  let W : H.Walk w y := p.append q
  have hbypass : W.bypass = r := congrArg Subtype.val
    (hH.isAcyclic.path_unique
      ⟨W.bypass, W.bypass_isPath⟩ ⟨r, geodesic_isPath H hH w y⟩)
  have hzW : z ∈ W.bypass.support := by
    rw [hbypass]
    simpa only [r] using hz
  have hzSupport : z ∈ W.support := W.support_bypass_subset_support hzW
  have hzParts : z ∈ p.support ∨ z ∈ q.support.tail := by
    simpa only [W, SimpleGraph.Walk.support_append, List.mem_append] using hzSupport
  rcases hzParts with hp | hq
  · left
    simpa only [p] using hp
  · right
    simpa only [q] using List.mem_of_mem_tail hq

/-- A vertex on the tree geodesic splits graph distance additively. -/
theorem dist_add_dist_eq_of_mem_geodesic {x y z : V}
    (hz : z ∈ (geodesic H hH x y).support) :
    H.dist x z + H.dist z y = H.dist x y := by
  classical
  let p := geodesic H hH x y
  let a := p.takeUntil z hz
  let b := p.dropUntil z hz
  have ha : H.dist x z ≤ a.length := SimpleGraph.dist_le a
  have hb : H.dist z y ≤ b.length := SimpleGraph.dist_le b
  have hab : a.length + b.length = H.dist x y := by
    rw [← SimpleGraph.Walk.length_append, p.take_spec hz]
    exact geodesic_length H hH x y
  have htri := hH.connected.dist_triangle (u := x) (v := z) (w := y)
  omega

/-- The `i`-th vertex of a tree geodesic is distance `i` from its start. -/
theorem dist_getVert_geodesic {x y : V} {i : ℕ} (hi : i ≤ H.dist x y) :
    H.dist x ((geodesic H hH x y).getVert i) = i := by
  let p := geodesic H hH x y
  let q := p.take i
  have hq : q.IsPath := (geodesic_isPath H hH x y).take i
  have hlength : q.length = i := by
    dsimp [q, p]
    rw [SimpleGraph.Walk.take_length, geodesic_length, min_eq_left hi]
  obtain ⟨r, hr, hrlength⟩ := hH.connected.exists_path_of_dist x (p.getVert i)
  have hqr : q = r := congrArg Subtype.val
    (hH.isAcyclic.path_unique ⟨q, hq⟩ ⟨r, hr⟩)
  change H.dist x (p.getVert i) = i
  calc
    H.dist x (p.getVert i) = r.length := hrlength.symm
    _ = q.length := congrArg SimpleGraph.Walk.length hqr.symm
    _ = i := hlength

/-- If an integral depth is at most twice the Gromov overlap of the two
rooted geodesics, the vertex at that depth on the second geodesic also lies on
the first.  This is the discrete branch-point lemma behind the four-point
estimate. -/
theorem getVert_mem_of_two_mul_le_overlap {w x y : V} {i : ℕ}
    (hi : i ≤ H.dist w y)
    (hoverlap : 2 * i + H.dist x y ≤ H.dist x w + H.dist y w) :
    (geodesic H hH w y).getVert i ∈ (geodesic H hH w x).support := by
  classical
  let v := (geodesic H hH w y).getVert i
  have hvwy : v ∈ (geodesic H hH w y).support :=
    SimpleGraph.Walk.getVert_mem_support _ _
  rcases mem_geodesic_left_or_right H hH (w := w) (x := x) (y := y) hvwy with
    hvwx | hvxy
  · exact hvwx
  · have hwy : H.dist w v + H.dist v y = H.dist w y :=
      dist_add_dist_eq_of_mem_geodesic H hH hvwy
    have hxy : H.dist x v + H.dist v y = H.dist x y :=
      dist_add_dist_eq_of_mem_geodesic H hH hvxy
    have hwv : H.dist w v = i := by
      dsimp [v]
      exact dist_getVert_geodesic H hH hi
    have htri := hH.connected.dist_triangle (u := w) (v := v) (w := x)
    have hxw : H.dist x w = H.dist w x := SimpleGraph.dist_comm
    have hyw : H.dist y w = H.dist w y := SimpleGraph.dist_comm
    have hxv : H.dist x v = H.dist v x := SimpleGraph.dist_comm
    have heq : H.dist w x = i + H.dist v x := by
      omega
    let a := geodesic H hH w v
    let b := geodesic H hH v x
    let q : H.Walk w x := a.append b
    have hqlength : q.length = H.dist w x := by
      dsimp [q, a, b]
      simp only [SimpleGraph.Walk.length_append, geodesic_length]
      omega
    have hqpath : q.IsPath := q.isPath_of_length_eq_dist hqlength
    have hqeq : q = geodesic H hH w x := congrArg Subtype.val
      (hH.isAcyclic.path_unique ⟨q, hqpath⟩
        ⟨geodesic H hH w x, geodesic_isPath H hH w x⟩)
    rw [← hqeq]
    exact (SimpleGraph.Walk.support_subset_support_append_left a b) a.end_mem_support

/-- **The integer four-point inequality for a tree, with unit slack.**

After division by two and casting graph distance to `ℝ`, this is exactly
Gromov's four-point inequality with hyperbolicity constant `1`.  The unit
slack avoids a parity argument; tree bipartiteness sharpens it to zero, but
the present form is already sufficient for Hull's hypotheses. -/
theorem graphDist_fourPoint_one (hH : H.IsTree) (w x y z : V) :
    min (H.dist x w + H.dist y w - H.dist x y)
        (H.dist y w + H.dist z w - H.dist y z) ≤
      H.dist x w + H.dist z w - H.dist x z + 2 := by
  classical
  let A := H.dist x w + H.dist y w - H.dist x y
  let B := H.dist y w + H.dist z w - H.dist y z
  let k := min A B / 2
  let v := (geodesic H hH w y).getVert k
  have hxyTri := hH.connected.dist_triangle (u := x) (v := w) (w := y)
  have hyzTri := hH.connected.dist_triangle (u := y) (v := w) (w := z)
  have hxzTri := hH.connected.dist_triangle (u := x) (v := w) (w := z)
  have hxwy := hH.connected.dist_triangle (u := x) (v := y) (w := w)
  have hxyTri' : H.dist x y ≤ H.dist x w + H.dist y w := by
    simpa only [SimpleGraph.dist_comm (u := w) (v := y)] using hxyTri
  have hyzTri' : H.dist y z ≤ H.dist y w + H.dist z w := by
    simpa only [SimpleGraph.dist_comm (u := w) (v := z)] using hyzTri
  have hxzTri' : H.dist x z ≤ H.dist x w + H.dist z w := by
    simpa only [SimpleGraph.dist_comm (u := w) (v := z)] using hxzTri
  have hAadd : A + H.dist x y = H.dist x w + H.dist y w := by
    dsimp [A]
    exact Nat.sub_add_cancel hxyTri'
  have hBadd : B + H.dist y z = H.dist y w + H.dist z w := by
    dsimp [B]
    exact Nat.sub_add_cancel hyzTri'
  have hkA : 2 * k ≤ A := by dsimp [k]; omega
  have hkB : 2 * k ≤ B := by dsimp [k]; omega
  have hkY : k ≤ H.dist w y := by
    have hywsym : H.dist y w = H.dist w y := SimpleGraph.dist_comm
    omega
  have hkxy : 2 * k + H.dist x y ≤ H.dist x w + H.dist y w := by
    omega
  have hkyz : 2 * k + H.dist y z ≤ H.dist y w + H.dist z w := by
    omega
  have hvx : v ∈ (geodesic H hH w x).support := by
    dsimp [v]
    exact getVert_mem_of_two_mul_le_overlap H hH hkY hkxy
  have hvz : v ∈ (geodesic H hH w z).support := by
    dsimp [v]
    exact getVert_mem_of_two_mul_le_overlap H hH hkY
      (by simpa only [SimpleGraph.dist_comm, add_comm] using hkyz)
  have hwv : H.dist w v = k := by
    dsimp [v]
    exact dist_getVert_geodesic H hH hkY
  have hwx : H.dist w v + H.dist v x = H.dist w x :=
    dist_add_dist_eq_of_mem_geodesic H hH hvx
  have hwz : H.dist w v + H.dist v z = H.dist w z :=
    dist_add_dist_eq_of_mem_geodesic H hH hvz
  have hxzV := hH.connected.dist_triangle (u := x) (v := v) (w := z)
  have htwok : 2 * k ≤ H.dist x w + H.dist z w - H.dist x z := by
    have hxwsym : H.dist x w = H.dist w x := SimpleGraph.dist_comm
    have hzwsym : H.dist z w = H.dist w z := SimpleGraph.dist_comm
    have hxvsym : H.dist x v = H.dist v x := SimpleGraph.dist_comm
    have hCadd :
        (H.dist x w + H.dist z w - H.dist x z) + H.dist x z =
          H.dist x w + H.dist z w := Nat.sub_add_cancel hxzTri'
    omega
  have hround : min A B < 2 * k + 2 := by
    dsimp [k]
    omega
  dsimp [A, B] at hround htwok ⊢
  omega

end TreeGraphGeometry
end GroupApproximation
