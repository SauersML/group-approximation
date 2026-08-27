import GroupApproximation.GGT.BassSerreDoubleHNN
import GroupApproximation.GGT.HyperbolicTreeAction
import GroupApproximation.GGT.WPDMinasyanOsinSkeleton

/-!
# `SkeletonAH3Input` from the Bass--Serre tree, modulo Minasyan--Osin's
Corollary 4.3

`GGT/WPDMinasyanOsinSkeleton.lean` reduces the manuscript's Minasyan--Osin
citation to two propositions: Osin's Theorem 1.2, and `SkeletonAH3Input` --- a
`GGT.AH3Data` for `Skeleton f hf`.  This module supplies the second one from the
Bass--Serre tree of `GGT/BassSerreHNNTree.lean`, with a single named gap.

## What the gap is, and what it is not

Three of the four geometric fields of `AH3Data` are unconditional here:
`isometric` and `hyperbolic` (`δ = 0`, through `GGT.isHyperbolicSpace_zero` on
`tree_isTree`) and `loxodromic` (`u₂u₁⁻¹` is a one-syllable cyclically reduced
word, so it translates by one).  The fourth, `wpd`, is
`TreeCorollary43` applied to the pair `(x₀, h²·x₀)`:

> **Minasyan--Osin, Corollary 4.3.**  Let `G` act on a simplicial tree and let
> `h ∈ G` be hyperbolic.  If `PStab_G({u,v})` is finite for some vertices
> `u, v` on the axis of `h`, then `h` satisfies the WPD condition.

Its engine is their Lemma 4.2 --- an `ε`-stabiliser of a distant pair sits in
boundedly many left cosets of the pointwise stabiliser of a middle pair --- and
that is the part this development does not carry out.  Everything Corollary 4.3
*consumes* is proved below, unconditionally:

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

/-! ## Minasyan--Osin's Corollary 4.3, named -/

/-- **Minasyan--Osin, *Acylindrical hyperbolicity of groups acting on trees*,
Math. Ann. 362 (2015), Corollary 4.3**, verbatim:

> Let `G` act on a simplicial tree `T` and let `h ∈ G` be hyperbolic.  Suppose
> that for some vertices `u, v ∈ axis(h)`, `PStab_G({u,v})` is finite (`u = v`
> is allowed).  Then `h` satisfies the WPD condition.

Here the two axis vertices are taken to be `x` and `hᴺ·x`, which are on the
axis for free once `h` is loxodromic at `x`.  The proof in the source is their
Lemma 4.2: for `d(x,y) > 2ε` the set `PStab^ε_G({x,y})` is contained in at most
`2(2ε+1)` left cosets of `PStab_G({u,v})` for suitable interior `u,v`, which is
the tree geometry this development does not carry out.
`GGT.isWPDAt_of_pairStab_cover` is the bookkeeping half, and it is proved.

Everything this proposition consumes about `Skeleton f hf` is proved in
`BassSerreDoubleHNN` below. -/
def TreeCorollary43 : Prop :=
  ∀ (Γ : Type) [Group Γ] (V : Type) (H : SimpleGraph V) (hH : H.IsTree)
    [MulAction Γ V],
    (∀ (a : Γ) (p q : V), H.dist (a • p) (a • q) = H.dist p q) →
    ∀ (g : Γ) (x : V) (N : ℕ),
      IsLoxodromic g (TreeSpace.of hH x) →
      (pairStab Γ 0 (TreeSpace.of hH x)
        ((g ^ N) • TreeSpace.of hH x)).Finite →
      IsWPDAt g (TreeSpace.of hH x)

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

/-! ## The `(AH₃)` datum, and `SkeletonAH3Input` -/

/-- **`u₂u₁⁻¹` is a WPD element**, granted Minasyan--Osin's Corollary 4.3. -/
theorem isWPDAt_axisElt (hcor : TreeCorollary43)
    (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1) :
    IsWPDAt (axisElt hj₁ hj₂)
      (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1) :=
  hcor (Double j₁ j₂ hj₁ hj₂)
    (BassSerreHNN.Vertex (stageTwoEquiv j₁ j₂ hj₁ hj₂))
    (BassSerreHNN.tree (stageTwoEquiv j₁ j₂ hj₁ hj₂))
    (BassSerreHNN.tree_isTree (stageTwoEquiv j₁ j₂ hj₁ hj₂))
    (BassSerreHNN.graph_dist_smul (stageTwoEquiv j₁ j₂ hj₁ hj₂))
    (axisElt hj₁ hj₂)
    (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1) 2
    (isLoxodromic_axisElt hj₁ hj₂)
    (pairStab_axis_finite hj₁ hj₂ hinter)

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

/-- **`SkeletonAH3Input` from the Bass--Serre tree.**  This is the target
`GGT/WPDMinasyanOsinSkeleton.lean` names; with it and Osin's Theorem 1.2 the
manuscript's Minasyan--Osin citation is discharged. -/
theorem skeletonAH3Input_of (hcor : TreeCorollary43) : SkeletonAH3Input.{0} := by
  intro P S instP instS f hf
  exact ⟨ah3DataOfWPD (factorOne_injective f hf) (factorTwo_injective f hf)
    (isWPDAt_axisElt hcor (factorOne_injective f hf) (factorTwo_injective f hf)
      (skeleton_inter f hf))⟩

/-- **The manuscript's Minasyan--Osin citation, from two named inputs.** -/
theorem minasyanOsinStatement_of_tree (hOsin : OsinTheorem12.{0, 0})
    (hcor : TreeCorollary43) : MinasyanOsinStatement :=
  minasyanOsinStatement_of hOsin (skeletonAH3Input_of hcor)

end BassSerreDoubleHNN
end GGT
end GroupApproximation
