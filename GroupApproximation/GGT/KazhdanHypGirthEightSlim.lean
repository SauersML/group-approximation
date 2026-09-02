import GroupApproximation.Algebra.HyperbolicSlimFourPoint
import GroupApproximation.GGT.KazhdanHypGirthEightDiagram

/-!
# The metric window in the linear-isoperimetric hyperbolicity argument

This file proves two parts of the passage from the linear disc inequality in
`GGT/KazhdanHypGirthEightDiagram.lean` to slim triangles.

First, a point of one side of a geodesic triangle which is more than `R` from
both other sides has a centered geodesic window.  Moving by at most `r` inside
that window leaves every point more than `R - r` from the other sides.  This is
the metric truncation used at the beginning of Bridson--Haefliger, III.H,
Theorem 2.9 and Papasoglu, Theorem 3.22:

* Bridson--Haefliger, *Metric Spaces of Non-Positive Curvature*, III.H.2.9,
  pages 419--421;
* Michael Batty, after Panagiotis Papasoglu, *Notes on Hyperbolic and
  Automatic Groups*, Theorem 3.22, pages 26--27.

Second, `girthEight_layer_depth_bound` combines disjoint star layers with the
proved inequality `innerFaceCount <= 3 * boundaryLength`.  If a boundary
segment has length `ell`, each of `m` disjoint layers contains enough faces to
satisfy `ell - loss <= rho * layer i`, and the whole boundary has length at
most `6 * ell`, then

`m * (ell - loss) <= 18 * rho * ell`.

This is the numerical contradiction at the end of the cited proofs.  The
remaining construction is topological: successive stars of the long boundary
segment must be represented as disjoint sets of inner faces.  The present
`VanKampen.DiscDiagram` has face permutations and face words, but it has no
vertex labelling in the Cayley graph and no boundary-subpath or star operation,
so that construction cannot yet be stated for it.
-/

namespace GroupApproximation
namespace GGT
namespace GirthEightSlim

open GroupApproximation.WordMetric
open scoped BigOperators

universe u w

variable {G : Type u} [Group G]

/-! ## Betweenness calculus -/

/-- A point between two endpoints is no farther from the left endpoint than
the endpoints are from one another. -/
theorem wordDist_left_le_of_isBetween {S : Set G} {x p y : G}
    (hp : Hyperbolic.IsBetween S x p y) :
    wordDist S x p <= wordDist S x y := by
  have h : wordDist S x p + wordDist S p y = wordDist S x y := hp
  omega

/-- A point between two endpoints is no farther from the right endpoint than
the endpoints are from one another. -/
theorem wordDist_right_le_of_isBetween {S : Set G} {x p y : G}
    (hp : Hyperbolic.IsBetween S x p y) :
    wordDist S p y <= wordDist S x y := by
  have h : wordDist S x p + wordDist S p y = wordDist S x y := hp
  omega

/-- A point between the left endpoint and a between-point remains between the
original endpoints. -/
theorem isBetween_trans_left {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {x q p y : G} (hp : Hyperbolic.IsBetween S x p y)
    (hq : Hyperbolic.IsBetween S x q p) :
    Hyperbolic.IsBetween S x q y := by
  have hp' : wordDist S x p + wordDist S p y = wordDist S x y := hp
  have hq' : wordDist S x q + wordDist S q p = wordDist S x p := hq
  have hqy := wordDist_triangle hS q p y
  have hxy := wordDist_triangle hS x q y
  unfold Hyperbolic.IsBetween
  omega

/-- A point between a between-point and the right endpoint remains between the
original endpoints. -/
theorem isBetween_trans_right {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {x p q y : G} (hp : Hyperbolic.IsBetween S x p y)
    (hq : Hyperbolic.IsBetween S p q y) :
    Hyperbolic.IsBetween S x q y := by
  have hp' : wordDist S x p + wordDist S p y = wordDist S x y := hp
  have hq' : wordDist S p q + wordDist S q y = wordDist S p y := hq
  have hxq := wordDist_triangle hS x p q
  have hxy := wordDist_triangle hS x q y
  unfold Hyperbolic.IsBetween
  omega

/-- Move a prescribed distance towards the left endpoint while staying on the
same geodesic side. -/
theorem exists_isBetween_before {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {x p y : G} (hp : Hyperbolic.IsBetween S x p y) {r : ℕ}
    (hr : r <= wordDist S x p) :
    ∃ q : G, Hyperbolic.IsBetween S x q p ∧
      Hyperbolic.IsBetween S x q y ∧ wordDist S q p = r := by
  obtain ⟨q, hq, hqx⟩ :=
    Hyperbolic.exists_isBetween hS x p (Nat.sub_le (wordDist S x p) r)
  have hq' : wordDist S x q + wordDist S q p = wordDist S x p := hq
  refine ⟨q, hq, isBetween_trans_left hS hp hq, ?_⟩
  omega

/-- Move a prescribed distance towards the right endpoint while staying on the
same geodesic side. -/
theorem exists_isBetween_after {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {x p y : G} (hp : Hyperbolic.IsBetween S x p y) {r : ℕ}
    (hr : r <= wordDist S p y) :
    ∃ q : G, Hyperbolic.IsBetween S p q y ∧
      Hyperbolic.IsBetween S x q y ∧ wordDist S p q = r := by
  obtain ⟨q, hq, hpq⟩ := Hyperbolic.exists_isBetween hS p y hr
  exact ⟨q, hq, isBetween_trans_right hS hp hq, hpq⟩

/-! ## Stability of separation under a short move -/

/-- If `p` is more than `R` from a geodesic side, a point at distance at most
`r` from `p` is more than `R - r` from that side. -/
theorem far_from_side_of_wordDist_le {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {p p' a b : G} {R r : ℕ}
    (hfar : ∀ q : G, Hyperbolic.IsBetween S a q b → R < wordDist S p q)
    (hclose : wordDist S p p' <= r) :
    ∀ q : G, Hyperbolic.IsBetween S a q b → R - r < wordDist S p' q := by
  intro q hq
  have hpq := hfar q hq
  have htri := wordDist_triangle hS p p' q
  omega

/-- A point far from the two opposite sides is farther than `R` from both
endpoints of its own side.  The two endpoints themselves lie on the opposite
sides. -/
theorem endpoint_margins_of_far_from_other_sides {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {x p y z : G} {R : ℕ}
    (hfarXZ : ∀ q : G,
      Hyperbolic.IsBetween S x q z → R < wordDist S p q)
    (hfarZY : ∀ q : G,
      Hyperbolic.IsBetween S z q y → R < wordDist S p q) :
    R < wordDist S x p ∧ R < wordDist S p y := by
  have hx := hfarXZ x (Hyperbolic.isBetween_left S x z)
  have hy := hfarZY y (Hyperbolic.isBetween_right z y)
  have hcomm := wordDist_comm hS p x
  omega

/-- **The centered separated window.**

If `p` is an `R`-far point on `[x,y]`, and `r` fits on both sides of `p`, there
are points `u,p,v` on `[x,y]` with `d(u,p)=d(p,v)=r`.  All three relevant
endpoint relations are retained, and `u` and `v` remain more than `R-r` from
both opposite sides. -/
theorem exists_centered_far_window {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {x p y z : G} {R r : ℕ}
    (hp : Hyperbolic.IsBetween S x p y)
    (hrLeft : r <= wordDist S x p) (hrRight : r <= wordDist S p y)
    (hfarXZ : ∀ q : G,
      Hyperbolic.IsBetween S x q z → R < wordDist S p q)
    (hfarZY : ∀ q : G,
      Hyperbolic.IsBetween S z q y → R < wordDist S p q) :
    ∃ u v : G,
      Hyperbolic.IsBetween S x u p ∧
      Hyperbolic.IsBetween S p v y ∧
      Hyperbolic.IsBetween S x u y ∧
      Hyperbolic.IsBetween S x v y ∧
      wordDist S u p = r ∧ wordDist S p v = r ∧
      wordDist S u v = 2 * r ∧
      (∀ q : G,
        Hyperbolic.IsBetween S x q z → R - r < wordDist S u q) ∧
      (∀ q : G,
        Hyperbolic.IsBetween S z q y → R - r < wordDist S u q) ∧
      (∀ q : G,
        Hyperbolic.IsBetween S x q z → R - r < wordDist S v q) ∧
      (∀ q : G,
        Hyperbolic.IsBetween S z q y → R - r < wordDist S v q) := by
  obtain ⟨u, huxp, huxy, hup⟩ := exists_isBetween_before hS hp hrLeft
  obtain ⟨v, hpvy, hvxy, hpv⟩ := exists_isBetween_after hS hp hrRight
  have hpu : wordDist S p u = r := by
    rw [wordDist_comm hS]
    exact hup
  have hfarUXZ := far_from_side_of_wordDist_le hS hfarXZ (le_of_eq hpu)
  have hfarUZY := far_from_side_of_wordDist_le hS hfarZY (le_of_eq hpu)
  have hfarVXZ := far_from_side_of_wordDist_le hS hfarXZ (le_of_eq hpv)
  have hfarVZY := far_from_side_of_wordDist_le hS hfarZY (le_of_eq hpv)
  have huvUpper := wordDist_triangle hS u p v
  have hxuv := wordDist_triangle hS x u v
  have hp' : wordDist S x p + wordDist S p y = wordDist S x y := hp
  have huxp' : wordDist S x u + wordDist S u p = wordDist S x p := huxp
  have hpvy' : wordDist S p v + wordDist S v y = wordDist S p y := hpvy
  have hvxy' : wordDist S x v + wordDist S v y = wordDist S x y := hvxy
  have huv : wordDist S u v = 2 * r := by omega
  exact ⟨u, v, huxp, hpvy, huxy, hvxy, hup, hpv, huv,
    hfarUXZ, hfarUZY, hfarVXZ, hfarVZY⟩

/-- An `R`-far point always has the centered window of radius `R / 2`.  The
endpoint-margin lemma supplies the two fit conditions. -/
theorem exists_half_radius_far_window {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {x p y z : G} {R : ℕ}
    (hp : Hyperbolic.IsBetween S x p y)
    (hfarXZ : ∀ q : G,
      Hyperbolic.IsBetween S x q z → R < wordDist S p q)
    (hfarZY : ∀ q : G,
      Hyperbolic.IsBetween S z q y → R < wordDist S p q) :
    ∃ u v : G,
      Hyperbolic.IsBetween S x u p ∧
      Hyperbolic.IsBetween S p v y ∧
      Hyperbolic.IsBetween S x u y ∧
      Hyperbolic.IsBetween S x v y ∧
      wordDist S u p = R / 2 ∧ wordDist S p v = R / 2 ∧
      wordDist S u v = 2 * (R / 2) ∧
      (∀ q : G, Hyperbolic.IsBetween S x q z →
        R - R / 2 < wordDist S u q) ∧
      (∀ q : G, Hyperbolic.IsBetween S z q y →
        R - R / 2 < wordDist S u q) ∧
      (∀ q : G, Hyperbolic.IsBetween S x q z →
        R - R / 2 < wordDist S v q) ∧
      (∀ q : G, Hyperbolic.IsBetween S z q y →
        R - R / 2 < wordDist S v q) := by
  obtain ⟨hx, hy⟩ := endpoint_margins_of_far_from_other_sides hS hfarXZ hfarZY
  apply exists_centered_far_window hS hp
  · omega
  · omega
  · exact hfarXZ
  · exact hfarZY

/-! ## The star-layer arithmetic -/

/-- If each of `m` layers contains enough faces to cover `ell - loss` after
multiplication by the face-perimeter bound `rho`, then their sum satisfies the
same lower bound multiplied by `m`. -/
theorem layer_sum_lower {m ell loss rho : ℕ} (layer : Fin m → ℕ)
    (hlayer : ∀ i, ell - loss <= rho * layer i) :
    m * (ell - loss) <= rho * ∑ i, layer i := by
  calc
    m * (ell - loss) = ∑ _i : Fin m, (ell - loss) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]
    _ <= ∑ i : Fin m, rho * layer i := by
      exact Finset.sum_le_sum fun i _hi => hlayer i
    _ = rho * ∑ i : Fin m, layer i := by
      rw [Finset.mul_sum]

/-- **Star depth allowed by the triangular girth-eight area inequality.**

The layer sets themselves are supplied as their cardinalities.  `hsum` is the
disjointness assertion: their sum is at most the number of inner faces.
`hlayer` is the boundary-covering assertion: a face has perimeter at most
`rho`, so a layer adjacent to a surviving segment needs enough faces to cover
`ell - loss`.  These two assertions are precisely what the successive-star
construction must prove from a diagram with a labelled boundary subpath. -/
theorem girthEight_layer_depth_bound
    {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : VanKampen.DiscDiagram W}
    (C : VanKampen.TriangularGirthEightDiagram Delta)
    {m ell loss rho : ℕ} (layer : Fin m → ℕ)
    (hperimeter : Delta.combinatorialBoundaryLength <= 6 * ell)
    (hsum : (∑ i, layer i) <= Delta.innerFaceCount)
    (hlayer : ∀ i, ell - loss <= rho * layer i) :
    m * (ell - loss) <= 18 * rho * ell := by
  calc
    m * (ell - loss) <= rho * ∑ i, layer i := layer_sum_lower layer hlayer
    _ <= rho * Delta.innerFaceCount := Nat.mul_le_mul_left rho hsum
    _ <= rho * (3 * Delta.combinatorialBoundaryLength) :=
      Nat.mul_le_mul_left rho C.innerFaceCount_le_three_mul_boundaryLength
    _ <= rho * (3 * (6 * ell)) :=
      Nat.mul_le_mul_left rho (Nat.mul_le_mul_left 3 hperimeter)
    _ = 18 * rho * ell := by ring

/-- A proposed family of disjoint star layers cannot have a lower bound larger
than the one forced by the linear area inequality. -/
theorem not_girthEight_layers_of_depth_gt
    {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : VanKampen.DiscDiagram W}
    (C : VanKampen.TriangularGirthEightDiagram Delta)
    {m ell loss rho : ℕ} (layer : Fin m → ℕ)
    (hperimeter : Delta.combinatorialBoundaryLength <= 6 * ell)
    (hsum : (∑ i, layer i) <= Delta.innerFaceCount)
    (hlayer : ∀ i, ell - loss <= rho * layer i)
    (hdepth : 18 * rho * ell < m * (ell - loss)) : False := by
  have hbound := girthEight_layer_depth_bound C layer hperimeter hsum hlayer
  omega

end GirthEightSlim
end GGT
end GroupApproximation
