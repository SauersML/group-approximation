import GroupApproximation.GGT.BassSerreDoubleHNN
import GroupApproximation.GGT.HyperbolicTreeAction
import GroupApproximation.GGT.WPDMinasyanOsinSkeleton

/-!
# The Bass--Serre tree data of `E`: the axis, and the trivial pair stabiliser

`GGT/WPDMinasyanOsinSkeleton.lean` reduces the manuscript's Minasyan--Osin
citation to two propositions: Osin's Theorem 1.2, and `SkeletonAH3Input` --- a
`GGT.AH3Data` for `Skeleton f hf`.  This module supplies what the Bass--Serre
tree of `GGT/BassSerreHNNTree.lean` contributes to the second one; the
assembly is `GGT.BassSerreDoubleHNN.skeletonAH3Input_unconditional` in
`GGT/TreeWPDAxis.lean`, which is unconditional.

## What is here

Three of the four geometric fields of `AH3Data` are immediate: `isometric` and
`hyperbolic` (`δ = 0`, through `GGT.isHyperbolicSpace_zero` on `tree_isTree`)
and `loxodromic` (`u₂u₁⁻¹` is a one-syllable cyclically reduced word, so it
translates by one).  The fourth, `wpd`, is Minasyan--Osin's Corollary 4.3 --- a
loxodromic whose axis carries a pair of vertices with finite pointwise
stabiliser is a WPD element --- proved in `GGT/TreeWPDAxis.lean` as
`GGT.isWPDAt_of_axis_pairStab_finite`.  What Corollary 4.3 *consumes* is proved
below:

* `pairStab_axis_finite` --- **`PStab_E({x₀, h²·x₀}) = 1`.**  Displacement
  convexity in a tree (`GGT.dist_smul_le_max_of_between`, proved by
  ggt-hyperbolic) turns fixing the two ends into fixing the middle vertex
  `h·x₀`, and the pointwise stabiliser of the three is
  `BassSerreDoubleHNN.eq_one_of_fixes_axis_segment`, i.e. `Δ₁ ∩ Δ₂ = 1`.
* `graph_dist_smul` --- the translation action preserves the graph distance,
  in the `∀ a p q, H.dist (a • p) (a • q) = H.dist p q` form the tree lemmas
  ask for.
* `tLen_axisElt_pow` --- `d(x₀, hⁿ·x₀) = n`, so `x₀` and `h²·x₀` really are on
  the axis and two apart.

## Two facts settled for the other lanes

The action of `E` on this tree is **not acylindrical** and the tree is **not
locally finite**: vertex stabilisers are the conjugates of `of(E₁)` and edge
stabilisers the conjugates of `ι(P)`, all infinite, and the pointwise stabiliser
of the segment `x₀, u₂·x₀, …, u₂ⁿ·x₀` is `ι(j₂ⁿ(P))`, infinite for every `n`
(`BassSerreHNN.mem_stabilizer_edge_iff` iterated).  So no
`TrivialSegmentStabilizers`-style hypothesis holds for this action, and the
Sela-style route is closed --- which is exactly why the argument runs through
WPD of the *single* element `u₂u₁⁻¹`, whose axis does carry a segment with
trivial pointwise stabiliser.
-/

namespace GroupApproximation
namespace GGT
namespace BassSerreHNN

open GroupApproximation.HullGeometry
open GroupApproximation.HNNBritton

universe u

variable {G : Type u} [Group G] {A B : Subgroup G}

/-! ## The action preserves the graph distance -/

/-- Left translation preserves the graph distance of the Bass--Serre tree, in
the shape `GGT.dist_smul_le_max_of_between` consumes. -/
theorem graph_dist_smul (φ : A ≃* B) (a : HNNExtension G A B φ)
    (p q : Vertex φ) :
    (tree φ).dist (a • p) (a • q) = (tree φ).dist p q := by
  obtain ⟨x, rfl⟩ := vmk_surjective φ p
  obtain ⟨y, rfl⟩ := vmk_surjective φ q
  have hkey : (a * x)⁻¹ * (a * y) = x⁻¹ * y := by group
  rw [smul_vmk, smul_vmk, dist_vmk, dist_vmk, hkey]

/-- **Fixing the ends of a geodesic fixes everything between them.**  This is
displacement convexity with both endpoint displacements zero. -/
theorem smul_eq_of_fixes_ends (φ : A ≃* B) (k : HNNExtension G A B φ)
    {x y m : Vertex φ}
    (hm : (tree φ).dist x m + (tree φ).dist m y = (tree φ).dist x y)
    (hx : k • x = x) (hy : k • y = y) : k • m = m := by
  have hb := GGT.dist_smul_le_max_of_between (tree_isTree φ)
    (graph_dist_smul φ) k hm
  rw [hx, hy, SimpleGraph.dist_self, SimpleGraph.dist_self, max_self] at hb
  have h0 : (tree φ).dist m (k • m) = 0 := Nat.le_zero.1 hb
  exact (((tree_connected φ).dist_eq_zero_iff).1 h0).symm

/-- An element moving a point of the metric tree by at most `0` fixes the
corresponding vertex. -/
theorem smul_vmk_eq_of_dist_le_zero (φ : A ≃* B)
    (k x : HNNExtension G A B φ) (h : dist (pt φ x) (k • pt φ x) ≤ 0) :
    k • vmk φ x = vmk φ x := by
  rw [smul_pt, dist_pt] at h
  have h1 : tLen φ (x⁻¹ * (k * x)) ≤ 0 := by exact_mod_cast h
  have h0 : tLen φ (x⁻¹ * (k * x)) = 0 := Nat.le_zero.1 h1
  refine (smul_vmk_eq_iff φ k x).2 ?_
  refine (tLen_eq_zero_iff φ _).1 ?_
  rw [mul_assoc]
  exact h0

end BassSerreHNN

namespace BassSerreDoubleHNN

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TheoremC

variable {P : Type} [Group P] {j₁ j₂ : P →* P}

/-! ## The axis, metrically -/

/-- **`u₂u₁⁻¹` translates by exactly one.** -/
theorem tLen_axisElt_pow (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) (n : ℕ) :
    BassSerreHNN.tLen (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂ ^ n)
      = n := by
  have h := BassSerreHNN.tLen_cyclicWord_pow (stageTwoEquiv j₁ j₂ hj₁ hj₂)
    (axisWord (j₂ := j₂) hj₁) n
  have hlen : ((axisWord (j₂ := j₂) hj₁).letters).length = 1 := rfl
  rw [axisWord_elem, hlen, mul_one] at h
  exact h

theorem tLen_axisElt (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    BassSerreHNN.tLen (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂) = 1 := by
  have h := tLen_axisElt_pow hj₁ hj₂ 1
  rwa [pow_one] at h

/-- **The base vertex lies on the axis of `u₂u₁⁻¹`**, in the graph-metric shape
Minasyan--Osin's Corollary 4.3 asks for: the orbit of `x₀` under the powers of
`u₂u₁⁻¹` is an arithmetic progression of step one along a geodesic.  Loxodromy
alone does not give this, and the difference is not cosmetic --- see the
counterexample in the docstring of `GGT/TreeWPDAxis.lean`. -/
theorem dist_vmk_axisElt_pow (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) (n : ℕ) :
    (BassSerreHNN.tree (stageTwoEquiv j₁ j₂ hj₁ hj₂)).dist
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
        ((axisElt hj₁ hj₂ ^ n) •
          BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
      = n * 1 := by
  rw [BassSerreHNN.smul_vmk, BassSerreHNN.dist_vmk_one, mul_one,
    tLen_axisElt_pow hj₁ hj₂ n, Nat.mul_one]

/-- The base vertex, `h·x₀` and `h²·x₀` sit on a geodesic in that order. -/
theorem axis_between (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    (BassSerreHNN.tree (stageTwoEquiv j₁ j₂ hj₁ hj₂)).dist
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂))
      + (BassSerreHNN.tree (stageTwoEquiv j₁ j₂ hj₁ hj₂)).dist
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂))
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ 2))
      = (BassSerreHNN.tree (stageTwoEquiv j₁ j₂ hj₁ hj₂)).dist
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ 2)) := by
  have e1 : (1 : Double j₁ j₂ hj₁ hj₂)⁻¹ * axisElt hj₁ hj₂
      = axisElt hj₁ hj₂ := by group
  have e2 : (axisElt hj₁ hj₂)⁻¹ * (axisElt hj₁ hj₂ ^ 2)
      = axisElt hj₁ hj₂ := by
    rw [pow_two]
    group
  have e3 : (1 : Double j₁ j₂ hj₁ hj₂)⁻¹ * (axisElt hj₁ hj₂ ^ 2)
      = axisElt hj₁ hj₂ ^ 2 := by group
  rw [BassSerreHNN.dist_vmk, BassSerreHNN.dist_vmk, BassSerreHNN.dist_vmk,
    e1, e2, e3]
  have h1 := tLen_axisElt hj₁ hj₂
  have h2 := tLen_axisElt_pow hj₁ hj₂ 2
  omega

/-! ## The pointwise stabiliser of the axis pair is trivial -/

/-- **`PStab_E({x₀, h²·x₀}) = 1`.**  Fixing the two ends fixes the middle vertex
by displacement convexity, and the pointwise stabiliser of the three is
`Δ₁ ∩ Δ₂ = 1`. -/
theorem eq_one_of_fixes_axis_ends (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1)
    (k : Double j₁ j₂ hj₁ hj₂)
    (h0 : k • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1
        = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
    (h2 : k • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ 2)
        = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ 2)) :
    k = 1 := by
  have hmid : k • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂)
      = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂) :=
    BassSerreHNN.smul_eq_of_fixes_ends (stageTwoEquiv j₁ j₂ hj₁ hj₂) k
      (axis_between hj₁ hj₂) h0 h2
  exact eq_one_of_fixes_axis_segment hj₁ hj₂ hinter k h0 hmid h2

theorem pairStab_axis_subset_one (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1) :
    pairStab (Double j₁ j₂ hj₁ hj₂) 0
        (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
        (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ 2))
      ⊆ {(1 : Double j₁ j₂ hj₁ hj₂)} := by
  intro k hk
  rw [mem_pairStab] at hk
  have hA := BassSerreHNN.smul_vmk_eq_of_dist_le_zero
    (stageTwoEquiv j₁ j₂ hj₁ hj₂) k 1 hk.1
  have hB := BassSerreHNN.smul_vmk_eq_of_dist_le_zero
    (stageTwoEquiv j₁ j₂ hj₁ hj₂) k (axisElt hj₁ hj₂ ^ 2) hk.2
  exact Set.mem_singleton_iff.2 (eq_one_of_fixes_axis_ends hj₁ hj₂ hinter k hA hB)

theorem pairStab_axis_finite (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1) :
    (pairStab (Double j₁ j₂ hj₁ hj₂) 0
        (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
        ((axisElt hj₁ hj₂ ^ 2) •
          BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)).Finite := by
  have hpt : (axisElt hj₁ hj₂ ^ 2) •
      BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1
    = BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ ^ 2) := by
    rw [BassSerreHNN.smul_pt, mul_one]
  rw [hpt]
  exact Set.Finite.subset (Set.finite_singleton _)
    (pairStab_axis_subset_one hj₁ hj₂ hinter)

/-! ## The `(AH₃)` datum -/

/-- **The `(AH₃)` datum of `E`**, from the WPD element. -/
noncomputable def ah3DataOfWPD (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hwpd : IsWPDAt (axisElt hj₁ hj₂)
      (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)) :
    AH3Data.{0, 0} (Double j₁ j₂ hj₁ hj₂) :=
  AH3Data.ofData (BassSerreHNN.Space (stageTwoEquiv j₁ j₂ hj₁ hj₂))
    (BassSerreHNN.isIsometricAction (stageTwoEquiv j₁ j₂ hj₁ hj₂)) 0
    (BassSerreHNN.isHyperbolicSpace_zero_space (stageTwoEquiv j₁ j₂ hj₁ hj₂))
    (axisElt hj₁ hj₂) (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
    (isLoxodromic_axisElt hj₁ hj₂) hwpd

end BassSerreDoubleHNN
end GGT
end GroupApproximation
