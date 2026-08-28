import GroupApproximation.GGT.BassSerreHNNWPDInput
import GroupApproximation.GGT.HyperbolicTreeSegmentShift

/-!
# Minasyan--Osin's Corollary 4.3 along an axis, and `SkeletonAH3Input`
unconditionally

`GGT/BassSerreHNNWPDInput.lean` reduced the manuscript's tree obligation to the
named proposition `TreeCorollary43`.  ggt-hyperbolic has since proved the tree
geometry that proposition was hiding --- `between_tripod`, `between_unique`,
`between_smul_of_middle`, `smul_eq_smul_of_dist_eq` and `exists_middle_pair` in
`GGT/HyperbolicTreeSegmentShift.lean` --- so the gap closes.  This module proves
Corollary 4.3 in the case the Bass--Serre argument uses, and with it
`SkeletonAH3Input` with **no** tree hypothesis left.

## The proof

`isWPDAt_of_axis` is Minasyan--Osin's Corollary 4.3 for an element translating
its axis by exactly one, with trivial pointwise stabilisers of two-step axis
pairs.  Given `ε`, take `n ≥ ε` and `M = 2n + 4`.

* `exists_middle_pair` produces `u`, `w` between `x` and `hᴹ·x`, at least two
  apart and strictly outside both `n`-collars.
* Every vertex between `x` and `hᴹ·x` is an axis vertex: it is `h^i·x` for
  `i` its distance from `x`, because both lie between the same two points at the
  same distance and `between_unique` identifies them.  This is the step that
  replaces Minasyan--Osin's "`u, v ∈ axis(h)`" side condition --- here it is a
  conclusion, not a hypothesis.
* So the pointwise stabiliser of `{u,w}` is that of a two-step axis pair, which
  is trivial by assumption.
* `Φ a = d(x, a·hᴹ·x)` is then injective on `PStab^ε({x, hᴹ·x})`: two elements
  with the same `Φ` agree on `u` and on `w` by `smul_eq_smul_of_dist_eq`, so
  their quotient fixes both and is `1`.  `Φ` is bounded by `M + n`, so the
  stabiliser injects into a finite set.

No coset arithmetic and no shift datum: triviality of the stabiliser makes `Φ`
injective outright, which is the same simplification ggt-hyperbolic exploits in
`isAcylindrical_treeSpace`.

## Why this does not also give acylindricity

The hypothesis `hstab` is about pairs **on the axis of `h`** only.  For `E`'s
tree the corresponding statement about *arbitrary* pairs is false: the pointwise
stabiliser of `x₀, u₂·x₀, …, u₂ⁿ·x₀` is `ι(j₂ⁿ(P)) ≅ P`, infinite.  That is the
gap between WPD and acylindricity, and it is why the manuscript's citation is
Minasyan--Osin's Theorem 2.1 route rather than a Sela-style one.

## The fixed-point set

`smul_eq_of_mem_geodesic` --- the fixed vertex set of any element is a subtree:
it is between-closed by displacement convexity, and the geodesic between two
fixed vertices therefore lies in it pointwise.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry

universe u v

/-! ## The fixed-point set is a subtree -/

/-- **The fixed vertex set of an isometry is a subtree.**  Every vertex of the
geodesic joining two fixed vertices is fixed. -/
theorem smul_eq_of_mem_geodesic {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree)
    (hiso : ∀ (a : G) (p q : V), H.dist (a • p) (a • q) = H.dist p q) (k : G)
    {x y z : V} (hx : k • x = x) (hy : k • y = y)
    (hz : z ∈ (TreeGraphGeometry.geodesic H hH x y).support) : k • z = z := by
  have hb : H.dist x z + H.dist z y = H.dist x y :=
    TreeGraphGeometry.dist_add_dist_eq_of_mem_geodesic H hH hz
  have hd := dist_smul_le_max_of_between hH hiso k hb
  rw [hx, hy, SimpleGraph.dist_self, SimpleGraph.dist_self, max_self] at hd
  have h0 : H.dist z (k • z) = 0 := Nat.le_zero.1 hd
  exact (eq_of_dist_eq_zero hH h0).symm

/-- **The fixed vertex set of an element of an HNN extension is a subtree**, in
the Bass--Serre tree of `GGT/BassSerreHNNTree.lean`. -/
theorem BassSerreHNN.smul_eq_of_mem_geodesic_tree {G : Type u} [Group G]
    {A B : Subgroup G} (φ : A ≃* B) (k : HNNExtension G A B φ)
    {x y z : BassSerreHNN.Vertex φ} (hx : k • x = x) (hy : k • y = y)
    (hz : z ∈ (TreeGraphGeometry.geodesic (BassSerreHNN.tree φ)
      (BassSerreHNN.tree_isTree φ) x y).support) : k • z = z :=
  smul_eq_of_mem_geodesic (BassSerreHNN.tree_isTree φ)
    (BassSerreHNN.graph_dist_smul φ) k hx hy hz

/-! ## Corollary 4.3 along an axis -/

/-- **Minasyan--Osin, Corollary 4.3, for a unit-translation axis.**

`h` translates its axis by one, and the pointwise stabiliser of any two axis
vertices at least two apart is trivial.  Then `h` is a WPD element. -/
theorem isWPDAt_of_axis {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree)
    (hadj : ∀ (a : G) (p q : V), H.Adj p q → H.Adj (a • p) (a • q))
    (g : G) (x : V)
    (hdist : ∀ m : ℕ, H.dist x ((g ^ m) • x) = m)
    (hstab : ∀ i j : ℕ, i + 2 ≤ j → ∀ k : G,
      k • ((g ^ i) • x) = (g ^ i) • x →
      k • ((g ^ j) • x) = (g ^ j) • x → k = 1) :
    IsWPDAt g (TreeSpace.of hH x) := by
  classical
  have hiso := dist_smul_eq hH hadj
  -- distances along the axis
  have hseg : ∀ i j : ℕ, i ≤ j →
      H.dist ((g ^ i) • x) ((g ^ j) • x) = j - i := by
    intro i j hij
    have hmul : (g ^ i) * (g ^ (j - i)) = g ^ j := by
      rw [← pow_add]
      congr 1
      omega
    have h1 : H.dist ((g ^ i) • x) ((g ^ j) • x)
        = H.dist ((g ^ i) • x) ((g ^ i) • ((g ^ (j - i)) • x)) := by
      rw [← mul_smul, hmul]
    rw [h1, hiso, hdist]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ε ≤ (n : ℝ) := ⟨⌈ε⌉₊, Nat.le_ceil ε⟩
  refine ⟨2 * n + 4, ?_⟩
  have hxy : H.dist x ((g ^ (2 * n + 4)) • x) = 2 * n + 4 := hdist _
  -- betweenness of the axis vertices
  have hbetween : ∀ i : ℕ, i ≤ 2 * n + 4 →
      H.dist x ((g ^ i) • x) + H.dist ((g ^ i) • x) ((g ^ (2 * n + 4)) • x)
        = H.dist x ((g ^ (2 * n + 4)) • x) := by
    intro i hi
    rw [hdist, hseg i (2 * n + 4) hi, hxy]
    omega
  -- every between-point is an axis vertex
  have haxis : ∀ m : V,
      H.dist x m + H.dist m ((g ^ (2 * n + 4)) • x)
        = H.dist x ((g ^ (2 * n + 4)) • x) → m = (g ^ (H.dist x m)) • x := by
    intro m hm
    have hi : H.dist x m ≤ 2 * n + 4 := by omega
    exact between_unique hH hm (hbetween _ hi) (hdist _).symm
  -- the middle pair
  obtain ⟨u, w, hLuw, ⟨hu2, hu3, hu4⟩, ⟨hw2, hw3, hw4⟩⟩ :=
    exists_middle_pair hH 2 n x ((g ^ (2 * n + 4)) • x) (by omega)
  obtain ⟨iu, hu⟩ : ∃ i : ℕ, u = (g ^ i) • x := ⟨_, haxis u hu2⟩
  obtain ⟨iw, hw⟩ : ∃ i : ℕ, w = (g ^ i) • x := ⟨_, haxis w hw2⟩
  -- the pointwise stabiliser of the middle pair is trivial
  have hstabuw : ∀ k : G, k • u = u → k • w = w → k = 1 := by
    intro k hku hkw
    rw [hu] at hku
    rw [hw] at hkw
    rcases le_total iu iw with hle | hle
    · have hd : H.dist u w = iw - iu := by
        rw [hu, hw]
        exact hseg iu iw hle
      exact hstab iu iw (by omega) k hku hkw
    · have hd : H.dist w u = iu - iw := by
        rw [hu, hw]
        exact hseg iw iu hle
      have hc : H.dist u w = H.dist w u := SimpleGraph.dist_comm
      exact hstab iw iu (by omega) k hkw hku
  -- the real distances on the metric tree
  have hval : ∀ a : G, dist (TreeSpace.of hH x) (a • TreeSpace.of hH x)
      = (H.dist x (a • x) : ℝ) := by
    intro a
    simp
  have hvaly : ∀ a : G,
      dist ((g ^ (2 * n + 4)) • TreeSpace.of hH x)
          (a • ((g ^ (2 * n + 4)) • TreeSpace.of hH x))
      = (H.dist ((g ^ (2 * n + 4)) • x) (a • ((g ^ (2 * n + 4)) • x)) : ℝ) := by
    intro a
    simp
  -- the two integer bounds available to a member of the stabiliser
  have hbx : ∀ a : G,
      a ∈ pairStab G ε (TreeSpace.of hH x)
        ((g ^ (2 * n + 4)) • TreeSpace.of hH x) →
      H.dist x (a • x) ≤ n := by
    intro a ha
    have h := ha.1
    rw [hval a] at h
    have h2 : (H.dist x (a • x) : ℝ) ≤ (n : ℝ) := le_trans h hn
    exact_mod_cast h2
  have hby : ∀ a : G,
      a ∈ pairStab G ε (TreeSpace.of hH x)
        ((g ^ (2 * n + 4)) • TreeSpace.of hH x) →
      H.dist ((g ^ (2 * n + 4)) • x) (a • ((g ^ (2 * n + 4)) • x)) ≤ n := by
    intro a ha
    have h := ha.2
    rw [hvaly a] at h
    have h2 : (H.dist ((g ^ (2 * n + 4)) • x)
        (a • ((g ^ (2 * n + 4)) • x)) : ℝ) ≤ (n : ℝ) := le_trans h hn
    exact_mod_cast h2
  -- the shift invariant is injective on the stabiliser
  refine Set.Finite.of_finite_image
    (f := fun a : G => H.dist x (a • ((g ^ (2 * n + 4)) • x))) ?_ ?_
  · refine Set.Finite.subset (Set.finite_Iic (2 * n + 4 + n)) ?_
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hby a ha
    have h2 := (hH.connected).dist_triangle (u := x)
      (v := (g ^ (2 * n + 4)) • x) (w := a • ((g ^ (2 * n + 4)) • x))
    simp only [Set.mem_Iic]
    omega
  · intro a ha b hb hab
    have hu' : a • u = b • u :=
      smul_eq_smul_of_dist_eq hH hiso a b (hbx a ha) (hby a ha) (hbx b hb)
        (hby b hb) hu2 hu3 hu4 hab
    have hw' : a • w = b • w :=
      smul_eq_smul_of_dist_eq hH hiso a b (hbx a ha) (hby a ha) (hbx b hb)
        (hby b hb) hw2 hw3 hw4 hab
    have hfu : (b⁻¹ * a) • u = u := by
      rw [mul_smul, hu', inv_smul_smul]
    have hfw : (b⁻¹ * a) • w = w := by
      rw [mul_smul, hw', inv_smul_smul]
    exact (inv_mul_eq_one.1 (hstabuw _ hfu hfw)).symm

end GGT
end GroupApproximation

namespace GroupApproximation
namespace GGT
namespace BassSerreDoubleHNN

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TheoremC

variable {P : Type} [Group P] {j₁ j₂ : P →* P}

/-! ## The axis of `u₂u₁⁻¹`, metrically -/

theorem dist_axis (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂)
    (i j : ℕ) (hij : i ≤ j) :
    (BassSerreHNN.tree (stageTwoEquiv j₁ j₂ hj₁ hj₂)).dist
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ i))
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ j))
      = j - i := by
  have hmul : (axisElt hj₁ hj₂ ^ i)⁻¹ * (axisElt hj₁ hj₂ ^ j)
      = axisElt hj₁ hj₂ ^ (j - i) := by
    have h : axisElt hj₁ hj₂ ^ i * axisElt hj₁ hj₂ ^ (j - i)
        = axisElt hj₁ hj₂ ^ j := by
      rw [← pow_add]
      congr 1
      omega
    rw [← h]
    group
  rw [BassSerreHNN.dist_vmk, hmul, tLen_axisElt_pow]

theorem smul_vmk_axis (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) (i : ℕ) :
    (axisElt hj₁ hj₂ ^ i) •
        BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1
      = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ ^ i) := by
  rw [BassSerreHNN.smul_vmk, mul_one]

/-! ## Trivial pointwise stabilisers along the axis -/

/-- The pointwise stabiliser of `x₀` and `hᵐ·x₀` for `m ≥ 2` is trivial:
displacement convexity pushes it down to `h²·x₀`. -/
theorem eq_one_of_fixes_zero_and (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1) (m : ℕ) (hm : 2 ≤ m)
    (k : Double j₁ j₂ hj₁ hj₂)
    (h0 : k • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1
        = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
    (hM : k • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ m)
        = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ m)) :
    k = 1 := by
  have hb : (BassSerreHNN.tree (stageTwoEquiv j₁ j₂ hj₁ hj₂)).dist
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ 2))
      + (BassSerreHNN.tree (stageTwoEquiv j₁ j₂ hj₁ hj₂)).dist
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ 2))
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ m))
      = (BassSerreHNN.tree (stageTwoEquiv j₁ j₂ hj₁ hj₂)).dist
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
        (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ m)) := by
    have e0 : (1 : Double j₁ j₂ hj₁ hj₂) = axisElt hj₁ hj₂ ^ 0 := by
      rw [pow_zero]
    rw [e0, dist_axis hj₁ hj₂ 0 2 (by omega),
      dist_axis hj₁ hj₂ 2 m hm, dist_axis hj₁ hj₂ 0 m (by omega)]
    omega
  have hmid : k • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ ^ 2)
      = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ ^ 2) :=
    BassSerreHNN.smul_eq_of_fixes_ends (stageTwoEquiv j₁ j₂ hj₁ hj₂) k hb h0 hM
  exact eq_one_of_fixes_axis_ends hj₁ hj₂ hinter k h0 hmid

/-- The pointwise stabiliser of any two axis vertices at least two apart is
trivial, by conjugating the previous statement along the axis. -/
theorem eq_one_of_fixes_axis_pair (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1) (i j : ℕ) (hij : i + 2 ≤ j)
    (k : Double j₁ j₂ hj₁ hj₂)
    (hi : k • ((axisElt hj₁ hj₂ ^ i) •
          BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
        = (axisElt hj₁ hj₂ ^ i) •
          BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
    (hj : k • ((axisElt hj₁ hj₂ ^ j) •
          BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
        = (axisElt hj₁ hj₂ ^ j) •
          BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1) :
    k = 1 := by
  have hmul : axisElt hj₁ hj₂ ^ i * axisElt hj₁ hj₂ ^ (j - i)
      = axisElt hj₁ hj₂ ^ j := by
    rw [← pow_add]
    congr 1
    omega
  have h0 : ((axisElt hj₁ hj₂ ^ i)⁻¹ * k * axisElt hj₁ hj₂ ^ i) •
      BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1
    = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1 := by
    rw [mul_smul, mul_smul, hi, inv_smul_smul]
  have hM : ((axisElt hj₁ hj₂ ^ i)⁻¹ * k * axisElt hj₁ hj₂ ^ i) •
      BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ ^ (j - i))
    = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ ^ (j - i)) := by
    rw [← smul_vmk_axis hj₁ hj₂ (j - i), ← mul_smul, mul_assoc, hmul,
      mul_smul, mul_smul, hj, ← mul_smul, ← hmul, inv_mul_cancel_left]
  have hone : (axisElt hj₁ hj₂ ^ i)⁻¹ * k * axisElt hj₁ hj₂ ^ i = 1 :=
    eq_one_of_fixes_zero_and hj₁ hj₂ hinter (j - i) (by omega) _ h0 hM
  have hconj := congrArg
    (fun z => axisElt hj₁ hj₂ ^ i * z * (axisElt hj₁ hj₂ ^ i)⁻¹) hone
  simpa [mul_assoc] using hconj

/-! ## The WPD element, and `SkeletonAH3Input`, unconditionally -/

/-- **`u₂u₁⁻¹` is a WPD element of the Bass--Serre action** --- no hypothesis. -/
theorem isWPDAt_axisElt' (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1) :
    IsWPDAt (axisElt hj₁ hj₂)
      (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1) := by
  refine isWPDAt_of_axis (BassSerreHNN.tree_isTree (stageTwoEquiv j₁ j₂ hj₁ hj₂))
    (fun a p q h => BassSerreHNN.adj_smul (stageTwoEquiv j₁ j₂ hj₁ hj₂) a h)
    (axisElt hj₁ hj₂)
    (BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1) ?_ ?_
  · intro m
    rw [smul_vmk_axis hj₁ hj₂ m]
    have h := dist_axis hj₁ hj₂ 0 m (Nat.zero_le m)
    rw [pow_zero] at h
    simpa using h
  · exact fun i j hij k hi hj => eq_one_of_fixes_axis_pair hj₁ hj₂ hinter i j hij k hi hj

/-- **The `(AH₃)` datum of `E`, unconditionally.** -/
noncomputable def ah3Data' (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1) :
    AH3Data.{0, 0} (Double j₁ j₂ hj₁ hj₂) :=
  ah3DataOfWPD hj₁ hj₂ (isWPDAt_axisElt' hj₁ hj₂ hinter)

/-- **`SkeletonAH3Input`, with no hypothesis.**  The Bass--Serre half of the
manuscript's Minasyan--Osin citation is discharged. -/
theorem skeletonAH3Input_axis : SkeletonAH3Input.{0} := by
  intro P S instP instS f hf
  exact ⟨ah3Data' (factorOne_injective f hf) (factorTwo_injective f hf)
    (skeleton_inter f hf)⟩

/-- **The manuscript's Minasyan--Osin citation, from Osin's Theorem 1.2
alone.** -/
theorem minasyanOsinStatement_of_osin_axis (hOsin : OsinTheorem12.{0, 0}) :
    MinasyanOsinStatement :=
  minasyanOsinStatement_of hOsin skeletonAH3Input_axis

end BassSerreDoubleHNN
end GGT
end GroupApproximation
