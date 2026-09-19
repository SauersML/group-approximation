import GroupApproximation.Algebra.HyperbolicSlimFourPoint
import GroupApproximation.GGT.KazhdanHypGirthEightFromDiagram

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

universe u v w

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
    (hr : r <= R)
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
    (hr : r <= R) (hrLeft : r <= wordDist S x p)
    (hrRight : r <= wordDist S p y)
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
  have hfarUXZ := far_from_side_of_wordDist_le hS hfarXZ hr (le_of_eq hpu)
  have hfarUZY := far_from_side_of_wordDist_le hS hfarZY hr (le_of_eq hpu)
  have hfarVXZ := far_from_side_of_wordDist_le hS hfarXZ hr (le_of_eq hpv)
  have hfarVZY := far_from_side_of_wordDist_le hS hfarZY hr (le_of_eq hpv)
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

/-! ## A finite symmetric alphabet from a finite generating tuple -/

/-- Adjoin the inverses of a finite generating tuple. -/
noncomputable def symmetrizedGeneratorFinset {Index : Type} [Fintype Index]
    (generator : Index → G) : Finset G := by
  classical
  exact Finset.univ.image generator ∪
    Finset.univ.image (fun i ↦ (generator i)⁻¹)

/-- Every value of the original tuple belongs to its finite
symmetrization. -/
theorem generator_mem_symmetrizedGeneratorFinset
    {Index : Type} [Fintype Index] (generator : Index → G) (i : Index) :
    generator i ∈ symmetrizedGeneratorFinset generator := by
  classical
  simp [symmetrizedGeneratorFinset]

/-- The finite symmetrization is closed under inversion and generates the
whole group whenever the original tuple does. -/
theorem symmetrizedGeneratorFinset_isSymmetricGeneratingSet
    {Index : Type} [Fintype Index] (generator : Index → G)
    (hgenerate : Subgroup.closure (Set.range generator) = ⊤) :
    IsSymmetricGeneratingSet
      ((symmetrizedGeneratorFinset generator : Finset G) : Set G) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [symmetrizedGeneratorFinset, Finset.mem_coe, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · right
      exact ⟨i, by rw [← hi]⟩
    · left
      exact ⟨i, by rw [← hi, inv_inv]⟩
  · have hrange : Set.range generator ⊆
        ((symmetrizedGeneratorFinset generator : Finset G) : Set G) := by
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact generator_mem_symmetrizedGeneratorFinset generator i
    apply le_antisymm le_top
    rw [← hgenerate]
    exact Subgroup.closure_mono hrange

/-! ## The exact successive-star input for slimness -/

/-- **The linear filling inequality gives slim triangles once successive
stars are constructed.**

The `build` hypothesis is precisely the topological step in the
Bridson--Haefliger/Papasoglu proof.  From a point on one side farther than
`delta` from both other sides, it supplies a disc diagram and disjoint
successive-star layer cardinalities.  The four final fields are exactly the
hypotheses of `not_girthEight_layers_of_depth_gt`, so the already proved
linear area bound rules out the far point.

For a triangular presentation, `build` is obtained by taking a centered
window from `exists_half_radius_far_window`, filling its boundary word, and
iterating face stars until one reaches an opposite side.  This construction
requires the boundary-subpath, Cayley-vertex-label, and face-star operations
not yet exposed by `VanKampen.DiscDiagram`. -/
theorem isSlimTriangles_of_girthEight_layer_construction
    {S : Set G} {delta : ℕ}
    {Base : Type v} [Group Base]
    {Lambda : Type w} {W : Set (List (GGT.RelLetter Base Lambda))}
    (build : ∀ x y z p : G,
      Hyperbolic.IsBetween S x p y →
      (∀ q : G, Hyperbolic.IsBetween S x q z →
        delta < wordDist S p q) →
      (∀ q : G, Hyperbolic.IsBetween S z q y →
        delta < wordDist S p q) →
      ∃ (Delta : VanKampen.DiscDiagram W)
        (_C : VanKampen.TriangularGirthEightDiagram Delta)
        (m ell loss rho : ℕ) (layer : Fin m → ℕ),
        Delta.combinatorialBoundaryLength <= 6 * ell ∧
        (∑ i, layer i) <= Delta.innerFaceCount ∧
        (∀ i, ell - loss <= rho * layer i) ∧
        18 * rho * ell < m * (ell - loss)) :
    Hyperbolic.IsSlimTriangles S delta := by
  classical
  intro x y z p hp
  by_contra hnear
  have hfarXZ : ∀ q : G, Hyperbolic.IsBetween S x q z →
      delta < wordDist S p q := by
    intro q hq
    by_contra hnot
    apply hnear
    exact Or.inl ⟨q, hq, by omega⟩
  have hfarZY : ∀ q : G, Hyperbolic.IsBetween S z q y →
      delta < wordDist S p q := by
    intro q hq
    by_contra hnot
    apply hnear
    exact Or.inr ⟨q, hq, by omega⟩
  obtain ⟨Delta, C, m, ell, loss, rho, layer,
    hperimeter, hsum, hlayer, hdepth⟩ :=
    build x y z p hp hfarXZ hfarZY
  exact not_girthEight_layers_of_depth_gt C layer hperimeter hsum hlayer hdepth

/-- A finite symmetric alphabet and the successive-star construction give the
repository's four-point definition of a hyperbolic group.  This is the final
metric step in Bridson--Haefliger III.H.2.9 after the topological layer
construction has supplied `build`. -/
theorem isHyperbolicGroup_of_girthEight_layer_construction
    {S : Finset G} {delta : ℕ}
    {Base : Type v} [Group Base]
    {Lambda : Type w} {W : Set (List (GGT.RelLetter Base Lambda))}
    (hS : IsSymmetricGeneratingSet (S : Set G))
    (build : ∀ x y z p : G,
      Hyperbolic.IsBetween (S : Set G) x p y →
      (∀ q : G, Hyperbolic.IsBetween (S : Set G) x q z →
        delta < wordDist (S : Set G) p q) →
      (∀ q : G, Hyperbolic.IsBetween (S : Set G) z q y →
        delta < wordDist (S : Set G) p q) →
      ∃ (Delta : VanKampen.DiscDiagram W)
        (_C : VanKampen.TriangularGirthEightDiagram Delta)
        (m ell loss rho : ℕ) (layer : Fin m → ℕ),
        Delta.combinatorialBoundaryLength <= 6 * ell ∧
        (∑ i, layer i) <= Delta.innerFaceCount ∧
        (∀ i, ell - loss <= rho * layer i) ∧
        18 * rho * ell < m * (ell - loss)) :
    Hyperbolic.IsHyperbolicGroup G :=
  Hyperbolic.isHyperbolicGroup_of_isSlimTriangles hS
    (isSlimTriangles_of_girthEight_layer_construction build)

/-! ## The specialization to a checked triangle table -/

section Presented

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- The canonical finite symmetric alphabet of a triangularly presented
group. -/
noncomputable def presentedGeneratorFinset
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    Finset (TriangularHodgeLayer.Presented T) :=
  symmetrizedGeneratorFinset (TriangularHodgeLayer.generator T)

/-- The canonical finite alphabet generates the triangularly presented
group. -/
theorem presentedGeneratorFinset_isSymmetricGeneratingSet
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    IsSymmetricGeneratingSet
      (↑(presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) :=
  symmetrizedGeneratorFinset_isSymmetricGeneratingSet
    (TriangularHodgeLayer.generator T)
    (TriangularHodgeLayer.closure_range_generator T)

/-- For one checked triangle table, a successive-star construction expressed
with the local reduced-diagram data proves hyperbolicity of the presented
group.  The conversion from `TriangularDiagramLocalData` to the curvature
package uses the link-girth theorem in
`KazhdanHypGirthEightFromDiagram.lean`. -/
theorem presented_isHyperbolicGroup_of_girthEight_layer_construction
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {d delta : ℕ} (hchecks : KazhdanHyp.GirthEightChecks T d)
    (build : ∀ x y z p : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x p y →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) x q z →
        delta < wordDist
          (↑(presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) z q y →
        delta < wordDist
          (↑(presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      ∃ (Delta : VanKampen.DiscDiagram (KazhdanHyp.triangleRelatorWords T))
        (_L : KazhdanHyp.TriangularDiagramLocalData T Delta)
        (m ell loss rho : ℕ) (layer : Fin m → ℕ),
        Delta.combinatorialBoundaryLength <= 6 * ell ∧
        (∑ i, layer i) <= Delta.innerFaceCount ∧
        (∀ i, ell - loss <= rho * layer i) ∧
        18 * rho * ell < m * (ell - loss)) :
    Hyperbolic.IsHyperbolicGroup
      (TriangularHodgeLayer.Presented T) := by
  apply isHyperbolicGroup_of_girthEight_layer_construction
    (S := presentedGeneratorFinset T) (delta := delta)
    (Base := FreeGroup Generator) (Lambda := PEmpty)
    (W := KazhdanHyp.triangleRelatorWords T)
    (presentedGeneratorFinset_isSymmetricGeneratingSet T)
  intro x y z p hp hfarXZ hfarZY
  obtain ⟨Delta, L, m, ell, loss, rho, layer,
    hperimeter, hsum, hlayer, hdepth⟩ :=
    build x y z p hp hfarXZ hfarZY
  exact ⟨Delta, L.toTriangularGirthEightDiagram hchecks,
    m, ell, loss, rho, layer, hperimeter, hsum, hlayer, hdepth⟩

end Presented

end GirthEightSlim
end GGT
end GroupApproximation
