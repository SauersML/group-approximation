import GroupApproximation.GGT.BassSerreHNNIsTree
import GroupApproximation.GGT.HyperbolicTreeMetric
import GroupApproximation.GGT.WPDElement

/-!
# The Bass--Serre tree of an HNN extension as a hyperbolic `G`-space

`GGT/BassSerreHNNIsTree.lean` proves that the Bass--Serre graph of
`HNNExtension G A B φ` is a tree; `GGT/HyperbolicTreeMetric.lean` turns any
tree into a `0`-hyperbolic metric space.  This module composes them and records
the two dynamical facts an `AH₃` datum needs.

* `Space φ`, `pt φ x` --- the tree as a metric space, and the point named by a
  group element.  `dist_pt` says the metric is the syllable length,
  `isIsometricAction` that translation preserves it, and
  `isHyperbolicSpace_zero` --- imported, not reproved --- that the space is
  `0`-hyperbolic.
* `isLoxodromic_cyclicWord` --- **a cyclically reduced word is a loxodromic
  isometry**, with translation length its syllable count.  This is
  `tLen_cyclicWord_pow` read as linear orbit growth: the `n`-th power of a
  cyclically reduced word of `k` syllables sits at distance exactly `nk` from
  the basepoint.
The weak proper discontinuity of `u₂u₁⁻¹` is no longer named here.  It is
Minasyan--Osin's Corollary 4.3, proved in `GGT/TreeWPDAxis.lean`
(`GGT.isWPDAt_of_axis_pairStab_finite`) from the shift invariant of
`GGT/HyperbolicTreeSegmentShift.lean`, and applied to the manuscript's `E` in
`GGT.BassSerreDoubleHNN.isWPDAt_axisElt_unconditional`.  Corollary 4.3 needs the
basepoint to lie on the axis of the element --- `d(x, hⁿ·x) = n · ℓ` --- and not
merely for it to be loxodromic; the criterion once stated here asked only for
loxodromy and was false for that reason, and the counterexample is recorded in
the docstring of `GGT/TreeWPDAxis.lean`.
-/

namespace GroupApproximation
namespace GGT
namespace BassSerreHNN

open GroupApproximation.HullGeometry

universe u

variable {G : Type u} [Group G] {A B : Subgroup G}

/-! ## The tree as a metric space -/

/-- **The Bass--Serre tree of `HNNExtension G A B φ` as a metric space.** -/
abbrev Space (φ : A ≃* B) : Type u := TreeSpace (tree_isTree φ)

instance instMulActionSpace (φ : A ≃* B) :
    MulAction (HNNExtension G A B φ) (Space φ) :=
  inferInstanceAs (MulAction (HNNExtension G A B φ) (Vertex φ))

/-- The point of the tree named by a group element: the vertex `xΔ`. -/
def pt (φ : A ≃* B) (x : HNNExtension G A B φ) : Space φ :=
  TreeSpace.of (tree_isTree φ) (vmk φ x)

@[simp] theorem smul_pt (φ : A ≃* B) (a x : HNNExtension G A B φ) :
    a • pt φ x = pt φ (a * x) := rfl

theorem pt_surjective (φ : A ≃* B) : Function.Surjective (pt φ) := by
  intro p
  obtain ⟨x, hx⟩ := vmk_surjective φ (TreeSpace.val p)
  refine ⟨x, ?_⟩
  show TreeSpace.of (tree_isTree φ) (vmk φ x) = p
  rw [hx, TreeSpace.of_val]

@[simp] theorem pt_eq_iff (φ : A ≃* B) (x y : HNNExtension G A B φ) :
    pt φ x = pt φ y ↔ vmk φ x = vmk φ y := Iff.rfl

/-- Fixing a point of the metric tree is fixing the vertex. -/
theorem smul_pt_eq_iff (φ : A ≃* B) (a x : HNNExtension G A B φ) :
    a • pt φ x = pt φ x ↔ a • vmk φ x = vmk φ x := by
  rw [smul_pt, pt_eq_iff, smul_vmk]

/-- **The metric of the Bass--Serre tree is the syllable length.** -/
@[simp] theorem dist_pt (φ : A ≃* B) (x y : HNNExtension G A B φ) :
    dist (pt φ x) (pt φ y) = (tLen φ (x⁻¹ * y) : ℝ) := by
  show dist (TreeSpace.of (tree_isTree φ) (vmk φ x))
      (TreeSpace.of (tree_isTree φ) (vmk φ y)) = (tLen φ (x⁻¹ * y) : ℝ)
  rw [TreeSpace.dist_of, dist_vmk]

theorem dist_pt_one (φ : A ≃* B) (y : HNNExtension G A B φ) :
    dist (pt φ 1) (pt φ y) = (tLen φ y : ℝ) := by
  rw [dist_pt]
  simp

/-- **Left translation is by isometries.** -/
theorem isIsometricAction (φ : A ≃* B) :
    IsIsometricAction (HNNExtension G A B φ) (Space φ) := by
  intro a p q
  obtain ⟨x, rfl⟩ := pt_surjective φ p
  obtain ⟨y, rfl⟩ := pt_surjective φ q
  have hkey : (a * x)⁻¹ * (a * y) = x⁻¹ * y := by group
  rw [smul_pt, smul_pt, dist_pt, dist_pt, hkey]

/-- **The Bass--Serre tree is `0`-hyperbolic.**  This is
`GGT.isHyperbolicSpace_zero` at `tree_isTree φ`; the four-point condition is
`TreeGraphGeometry.graphDist_fourPoint_one` with the parity slack removed. -/
theorem isHyperbolicSpace_zero_space (φ : A ≃* B) :
    IsHyperbolicSpace 0 (Space φ) :=
  GGT.isHyperbolicSpace_zero (tree_isTree φ)

/-! ## Loxodromic elements -/

/-- **A cyclically reduced word acts as a loxodromic isometry**, with
translation length its number of syllables. -/
theorem isLoxodromic_cyclicWord (φ : A ≃* B)
    (c : HNNTorsionFree.CyclicWord G A B) :
    IsLoxodromic (c.elem φ) (pt φ 1) := by
  refine ⟨(c.letters.length : ℝ), ?_, 0, le_rfl, ?_⟩
  · have hpos : 0 < c.letters.length := List.length_pos_iff.2 c.nonempty
    exact_mod_cast hpos
  · intro n
    have hd : dist (pt φ 1) ((c.elem φ ^ n) • pt φ 1)
        = ((n * c.letters.length : ℕ) : ℝ) := by
      rw [smul_pt, mul_one, dist_pt_one, tLen_cyclicWord_pow]
    have hcast : ((n * c.letters.length : ℕ) : ℝ)
        = (c.letters.length : ℝ) * (n : ℝ) := by
      push_cast
      ring
    rw [hd, hcast]
    linarith

end BassSerreHNN
end GGT
end GroupApproximation
