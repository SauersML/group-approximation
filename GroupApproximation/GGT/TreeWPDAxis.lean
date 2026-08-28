import GroupApproximation.GGT.BassSerreHNNWPDInput
import GroupApproximation.GGT.HyperbolicTreeSegmentShift

/-!
# Minasyan--Osin's Corollary 4.3, proved, and the hypothesis it needs

The tree half of the manuscript's Minasyan--Osin citation used to be carried by
two named propositions, `TreeCorollary43` in `GGT/BassSerreHNNWPDInput.lean` and
`IsTreeWPDCriterion` in `GGT/BassSerreHNNAction.lean`.  Both stated Corollary 4.3
with `IsLoxodromic h x` as the only hypothesis relating `h` to the basepoint `x`,
and **both were false in that form**.  This module proves Corollary 4.3 with the
hypothesis it needs, and `GGT.SkeletonAH3Input` outright; the two propositions
are deleted.

## Why the loxodromy hypothesis alone is not enough

Minasyan--Osin, *Acylindrical hyperbolicity of groups acting on trees*, Math.
Ann. 362 (2015), Corollary 4.3, asks for two vertices **on the axis of `h`**
with finite pointwise stabiliser.  `IsLoxodromic h x` is the lower bound
`l · n - B ≤ d(x, hⁿ·x)`, which holds for basepoints off the axis as well, and
off the axis a small stabiliser of `x` says nothing about the stabiliser of the
axis.

The counterexample: let `K` be an infinite group, `Γ = K × ℤ`, and let `π : Γ → ℤ`
be the projection.  Let `T` be the line `ℤ` together with one extra leaf `ℓ_γ`
for each `γ ∈ Γ`, the leaf `ℓ_γ` joined to the vertex `π γ`.  Then `T` is a tree,
`Γ` acts on it by graph automorphisms through `γ · n = n + π γ` and
`γ · ℓ_δ = ℓ_{γδ}`, and the action on the leaves is free.  Take `x = ℓ_1` and
`h = (1,1)`.  Then `d(x, hⁿ·x) = n + 2`, so `h` is loxodromic at `x`; the
stabiliser of `x` is trivial, so the pointwise stabiliser of any set containing
`x` is trivial; but for `ε = 2` and every `M`, each `k ∈ K` moves `x` and
`h^M·x` by exactly `2`, so `PStab^2_Γ({x, h^M·x})` contains `K` and `h` is not a
WPD element.

What the argument really needs is that the two vertices lie on the axis, which
is recorded here as `∀ m, d(x, gᵐ·x) = m · ℓ` with `0 < ℓ`: the orbit of `x`
under `⟨g⟩` is an arithmetic progression along a geodesic.  At the manuscript's
`E` this is `BassSerreDoubleHNN.tLen_axisElt_pow` with `ℓ = 1`, so nothing
downstream is weakened by the repair.

## What is proved

* `finite_epsStab_of_middle` --- **Minasyan--Osin's Lemma 4.2 with its coset
  count carried out**: if two vertices `u`, `w` lie between `x` and `y`, both
  strictly outside the `n`-collars of the segment, and the pointwise stabiliser
  of `{u,w}` is finite, then the set of elements moving both `x` and `y` by at
  most `n` is finite.  The invariant is the one
  `GGT/HyperbolicTreeSegmentShift.lean` already isolates,
  `Φ k = d(x,y) - d(x, k·y)`; it takes at most `2n + 1` values, and
  `smul_eq_smul_of_dist_eq` says its level sets are contained in left cosets of
  the pointwise stabiliser.
* `isWPDAt_of_axis_pairStab_finite` --- **Corollary 4.3**: for an axis basepoint,
  one pair `(x, g^N·x)` with finite pointwise stabiliser makes `g` a WPD
  element.  Given `ε`, the power used is `g^(N + 2⌈ε⌉ + 2)` and the middle pair
  is `(g^(⌈ε⌉+1)·x, g^(⌈ε⌉+1+N)·x)`, whose pointwise stabiliser is a conjugate
  of the given one.
* `isWPDAt_of_pairStab_zero_finite` --- the same with the finiteness hypothesis
  written as a `pairStab`, which is the shape a tree action delivers it in.
* `BassSerreDoubleHNN.isWPDAt_axisElt_unconditional` --- `u₂u₁⁻¹` is a WPD
  element for the Bass--Serre action of `E`, with no hypothesis but
  `Δ₁ ∩ Δ₂ = 1`.
* `BassSerreDoubleHNN.skeletonAH3Input_unconditional` ---
  **`GGT.SkeletonAH3Input`, proved**.

## What remains of the manuscript's citation

`minasyanOsinStatement_of_osinTheorem12`: the Minasyan--Osin input of
`thm:torsion-free` now rests on `GGT.OsinTheorem12` alone --- Osin's
`(AH₃) ⇒ (AH₁)`, which `GGT/WPDAcylindricalHyperbolicity.lean` reduces further
to Dahmani--Guirardel--Osin's Theorem 6.8 and Osin's Theorem 5.4.  Nothing about
trees is left in it.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.TreeGraphGeometry

universe u v

/-! ## Pointwise stabilisers of a pair of vertices -/

section Trees

variable {Γ : Type u} [Group Γ] {V : Type v} {H : SimpleGraph V} [MulAction Γ V]

/-- In a tree, lying in the `ε = 0` stabiliser of a pair of vertices is fixing
both of them: the graph metric is a genuine metric on vertices. -/
theorem mem_pairStab_zero_tree (hH : H.IsTree) {u w : V} {k : Γ} :
    k ∈ pairStab Γ 0 (TreeSpace.of hH u) (TreeSpace.of hH w) ↔
      (k • u = u ∧ k • w = w) := by
  rw [mem_pairStab]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : ((H.dist u (k • u) : ℕ) : ℝ) ≤ 0 := h1
    have e2 : ((H.dist w (k • w) : ℕ) : ℝ) ≤ 0 := h2
    have n1 : H.dist u (k • u) ≤ 0 := by exact_mod_cast e1
    have n2 : H.dist w (k • w) ≤ 0 := by exact_mod_cast e2
    exact ⟨(eq_of_dist_eq_zero hH (Nat.le_zero.mp n1)).symm,
      (eq_of_dist_eq_zero hH (Nat.le_zero.mp n2)).symm⟩
  · rintro ⟨h1, h2⟩
    constructor
    · show ((H.dist u (k • u) : ℕ) : ℝ) ≤ 0
      rw [h1, SimpleGraph.dist_self]
      norm_num
    · show ((H.dist w (k • w) : ℕ) : ℝ) ≤ 0
      rw [h2, SimpleGraph.dist_self]
      norm_num

/-! ## Minasyan--Osin's Lemma 4.2, with the coset count -/

/-- **The `n`-stabiliser of a long segment is finite as soon as the pointwise
stabiliser of a middle pair is.**

`u` and `w` lie between `x` and `y`, strictly outside the two `n`-collars.  An
element `k` moving `x` and `y` by at most `n` shifts the middle of the segment
by the integer `Φ k = d(x,y) - d(x, k·y)`, which the triangle inequality bounds
by `n` in absolute value, so it takes at most `2n + 1` values; and
`GGT.smul_eq_smul_of_dist_eq` says two elements with the same shift agree on `u`
and on `w`, so each level set lies in a left coset of `PStab_Γ({u,w})`.  A
finite union of finite sets is finite.

This is Minasyan--Osin's Lemma 4.2 together with the count their Corollary 4.3
performs on it. -/
theorem finite_epsStab_of_middle (hH : H.IsTree)
    (hiso : ∀ (a : Γ) (p q : V), H.dist (a • p) (a • q) = H.dist p q)
    {x y u w : V} {n : ℕ}
    (hbu : H.dist x u + H.dist u y = H.dist x y)
    (hu1 : n < H.dist x u) (hu2 : n < H.dist u y)
    (hbw : H.dist x w + H.dist w y = H.dist x y)
    (hw1 : n < H.dist x w) (hw2 : n < H.dist w y)
    (hK : {k : Γ | k • u = u ∧ k • w = w}.Finite) :
    {k : Γ | H.dist x (k • x) ≤ n ∧ H.dist y (k • y) ≤ n}.Finite := by
  classical
  have hfib : ∀ i : Fin (2 * n + 1),
      {k : Γ | (H.dist x (k • x) ≤ n ∧ H.dist y (k • y) ≤ n) ∧
        (H.dist x y : ℤ) - (H.dist x (k • y) : ℤ)
          = ((i : ℕ) : ℤ) - (n : ℤ)}.Finite := by
    intro i
    rcases Set.eq_empty_or_nonempty
        {k : Γ | (H.dist x (k • x) ≤ n ∧ H.dist y (k • y) ≤ n) ∧
          (H.dist x y : ℤ) - (H.dist x (k • y) : ℤ)
            = ((i : ℕ) : ℤ) - (n : ℤ)} with he | hne
    · rw [he]
      exact Set.finite_empty
    · obtain ⟨k₀, hk₀⟩ := hne
      refine (hK.image (fun z => k₀ * z)).subset ?_
      rintro k ⟨⟨hkx, hky⟩, hki⟩
      have h0 := hk₀.2
      have hd : H.dist x (k • y) = H.dist x (k₀ • y) := by omega
      have hu : k • u = k₀ • u :=
        smul_eq_smul_of_dist_eq hH hiso k k₀ hkx hky hk₀.1.1 hk₀.1.2 hbu hu1 hu2 hd
      have hw : k • w = k₀ • w :=
        smul_eq_smul_of_dist_eq hH hiso k k₀ hkx hky hk₀.1.1 hk₀.1.2 hbw hw1 hw2 hd
      refine ⟨k₀⁻¹ * k, ⟨?_, ?_⟩, ?_⟩
      · rw [mul_smul, hu, inv_smul_smul]
      · rw [mul_smul, hw, inv_smul_smul]
      · show k₀ * (k₀⁻¹ * k) = k
        group
  have hunion : (⋃ i : Fin (2 * n + 1),
      {k : Γ | (H.dist x (k • x) ≤ n ∧ H.dist y (k • y) ≤ n) ∧
        (H.dist x y : ℤ) - (H.dist x (k • y) : ℤ)
          = ((i : ℕ) : ℤ) - (n : ℤ)}).Finite :=
    Set.finite_iUnion hfib
  refine hunion.subset ?_
  rintro k ⟨hkx, hky⟩
  have t1 := hH.connected.dist_triangle (u := x) (v := y) (w := k • y)
  have t2 := hH.connected.dist_triangle (u := x) (v := k • y) (w := y)
  have c : H.dist (k • y) y = H.dist y (k • y) := SimpleGraph.dist_comm
  have hnn : (0 : ℤ) ≤ (H.dist x y : ℤ) - (H.dist x (k • y) : ℤ) + (n : ℤ) := by
    omega
  obtain ⟨j, hj⟩ : ∃ j : ℕ,
      (j : ℤ) = (H.dist x y : ℤ) - (H.dist x (k • y) : ℤ) + (n : ℤ) :=
    ⟨_, Int.toNat_of_nonneg hnn⟩
  have hjlt : j < 2 * n + 1 := by omega
  refine Set.mem_iUnion.mpr ⟨⟨j, hjlt⟩, ⟨hkx, hky⟩, ?_⟩
  show (H.dist x y : ℤ) - (H.dist x (k • y) : ℤ) = (j : ℤ) - (n : ℤ)
  omega

/-! ## Minasyan--Osin's Corollary 4.3 -/

/-- **Corollary 4.3, in its true form.**  Let `g` translate the basepoint `x`
along a geodesic by `ℓ > 0` at every power --- that is, let `x` lie on the axis
of `g` --- and let the pointwise stabiliser of the axis pair `(x, g^N·x)` be
finite.  Then `g` satisfies the WPD condition at `x`.

Given `ε`, put `n = ⌈ε⌉` and take the power `M = N + 2n + 2`.  The two vertices
`g^(n+1)·x` and `g^(n+1+N)·x` lie between `x` and `g^M·x` and are further than
`n` from both ends, because the translation length is at least one; their
pointwise stabiliser is the conjugate by `g^(n+1)` of the given one, hence
finite; and `finite_epsStab_of_middle` finishes.

The axis hypothesis is not decoration: without it the statement is false, and
the module docstring gives the counterexample. -/
theorem isWPDAt_of_axis_pairStab_finite (hH : H.IsTree)
    (hiso : ∀ (a : Γ) (p q : V), H.dist (a • p) (a • q) = H.dist p q)
    {g : Γ} {x : V} {ℓ N : ℕ} (hℓ : 0 < ℓ)
    (haxis : ∀ m : ℕ, H.dist x ((g ^ m) • x) = m * ℓ)
    (hfin : {k : Γ | k • x = x ∧ k • ((g ^ N) • x) = (g ^ N) • x}.Finite) :
    IsWPDAt g (TreeSpace.of hH x) := by
  classical
  have hl1 : 1 ≤ ℓ := by omega
  have hdist : ∀ p q : ℕ, p ≤ q →
      H.dist ((g ^ p) • x) ((g ^ q) • x) = (q - p) * ℓ := by
    intro p q hpq
    have hpow : p + (q - p) = q := by omega
    have hsplit : (g ^ p) • ((g ^ (q - p)) • x) = (g ^ q) • x := by
      rw [← mul_smul, ← pow_add, hpow]
    rw [← hsplit, hiso, haxis]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ε ≤ (n : ℝ) := ⟨⌈ε⌉₊, Nat.le_ceil ε⟩
  have hmul : ∀ c : ℕ, n < c → n < c * ℓ := by
    intro c hc
    have h1 : c * 1 ≤ c * ℓ := Nat.mul_le_mul_left c hl1
    rw [Nat.mul_one] at h1
    omega
  refine ⟨N + 2 * n + 2, ?_⟩
  have hxu : H.dist x ((g ^ (n + 1)) • x) = (n + 1) * ℓ := haxis (n + 1)
  have hxw : H.dist x ((g ^ (n + 1 + N)) • x) = (n + 1 + N) * ℓ := haxis (n + 1 + N)
  have hxy : H.dist x ((g ^ (N + 2 * n + 2)) • x) = (N + 2 * n + 2) * ℓ :=
    haxis (N + 2 * n + 2)
  have huy : H.dist ((g ^ (n + 1)) • x) ((g ^ (N + 2 * n + 2)) • x)
      = (N + 2 * n + 2 - (n + 1)) * ℓ :=
    hdist (n + 1) (N + 2 * n + 2) (by omega)
  have hwy : H.dist ((g ^ (n + 1 + N)) • x) ((g ^ (N + 2 * n + 2)) • x)
      = (N + 2 * n + 2 - (n + 1 + N)) * ℓ :=
    hdist (n + 1 + N) (N + 2 * n + 2) (by omega)
  have hbu : H.dist x ((g ^ (n + 1)) • x)
      + H.dist ((g ^ (n + 1)) • x) ((g ^ (N + 2 * n + 2)) • x)
      = H.dist x ((g ^ (N + 2 * n + 2)) • x) := by
    have he : n + 1 + (N + 2 * n + 2 - (n + 1)) = N + 2 * n + 2 := by omega
    rw [hxu, huy, hxy, ← add_mul, he]
  have hbw : H.dist x ((g ^ (n + 1 + N)) • x)
      + H.dist ((g ^ (n + 1 + N)) • x) ((g ^ (N + 2 * n + 2)) • x)
      = H.dist x ((g ^ (N + 2 * n + 2)) • x) := by
    have he : n + 1 + N + (N + 2 * n + 2 - (n + 1 + N)) = N + 2 * n + 2 := by omega
    rw [hxw, hwy, hxy, ← add_mul, he]
  have hu1 : n < H.dist x ((g ^ (n + 1)) • x) := by
    rw [hxu]
    exact hmul _ (by omega)
  have hu2 : n < H.dist ((g ^ (n + 1)) • x) ((g ^ (N + 2 * n + 2)) • x) := by
    rw [huy]
    exact hmul _ (by omega)
  have hw1 : n < H.dist x ((g ^ (n + 1 + N)) • x) := by
    rw [hxw]
    exact hmul _ (by omega)
  have hw2 : n < H.dist ((g ^ (n + 1 + N)) • x) ((g ^ (N + 2 * n + 2)) • x) := by
    rw [hwy]
    exact hmul _ (by omega)
  have hcomm : (g ^ (n + 1)) • ((g ^ N) • x) = (g ^ (n + 1 + N)) • x := by
    rw [← mul_smul, ← pow_add]
  have hK : {k : Γ | k • ((g ^ (n + 1)) • x) = (g ^ (n + 1)) • x ∧
      k • ((g ^ (n + 1 + N)) • x) = (g ^ (n + 1 + N)) • x}.Finite := by
    refine (hfin.image (fun z => g ^ (n + 1) * z * (g ^ (n + 1))⁻¹)).subset ?_
    rintro k ⟨h1, h2⟩
    refine ⟨(g ^ (n + 1))⁻¹ * k * g ^ (n + 1), ⟨?_, ?_⟩, ?_⟩
    · rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · rw [mul_smul, mul_smul, hcomm, h2, ← hcomm, inv_smul_smul]
    · show g ^ (n + 1) * ((g ^ (n + 1))⁻¹ * k * g ^ (n + 1)) * (g ^ (n + 1))⁻¹ = k
      group
  refine Set.Finite.subset
    (finite_epsStab_of_middle hH hiso hbu hu1 hu2 hbw hw1 hw2 hK) ?_
  intro k hk
  rw [mem_pairStab] at hk
  obtain ⟨h1, h2⟩ := hk
  have e1 : ((H.dist x (k • x) : ℕ) : ℝ) ≤ ε := h1
  have e2 : ((H.dist ((g ^ (N + 2 * n + 2)) • x)
      (k • ((g ^ (N + 2 * n + 2)) • x)) : ℕ) : ℝ) ≤ ε := h2
  exact ⟨by exact_mod_cast le_trans e1 hn, by exact_mod_cast le_trans e2 hn⟩

/-- **Corollary 4.3 with the finiteness hypothesis as a `pairStab`**, which is
the shape a tree action delivers it in: a tree, an action preserving the graph
metric, an axis basepoint, and one pair `(x, g^N·x)` with finite pointwise
stabiliser. -/
theorem isWPDAt_of_pairStab_zero_finite (hH : H.IsTree)
    (hiso : ∀ (a : Γ) (p q : V), H.dist (a • p) (a • q) = H.dist p q)
    (g : Γ) (x : V) (ℓ N : ℕ) (hℓ : 0 < ℓ)
    (haxis : ∀ m : ℕ, H.dist x ((g ^ m) • x) = m * ℓ)
    (hfin : (pairStab Γ 0 (TreeSpace.of hH x)
      ((g ^ N) • TreeSpace.of hH x)).Finite) :
    IsWPDAt g (TreeSpace.of hH x) := by
  refine isWPDAt_of_axis_pairStab_finite hH hiso hℓ haxis ?_
  refine hfin.subset ?_
  intro k hk
  exact (mem_pairStab_zero_tree (u := x) (w := (g ^ N) • x) hH).2 hk

end Trees

/-! ## At the manuscript's `E` -/

namespace BassSerreDoubleHNN

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TheoremC

variable {P : Type} [Group P] {j₁ j₂ : P →* P}

/-- **`PStab_E({x₀, h²·x₀}) = 1`**, in the vertex-fixing shape Corollary 4.3
consumes.  The two vertices are the ends of a segment of the axis, and the
pointwise stabiliser of that segment is `Δ₁ ∩ Δ₂ = 1`. -/
theorem pairStab_axis_vertex_finite (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1) :
    {k : Double j₁ j₂ hj₁ hj₂ |
        k • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1
          = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1 ∧
        k • ((axisElt hj₁ hj₂ ^ 2) •
            BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
          = (axisElt hj₁ hj₂ ^ 2) •
            BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1}.Finite := by
  refine Set.Finite.subset
    (Set.finite_singleton (1 : Double j₁ j₂ hj₁ hj₂)) ?_
  rintro k ⟨h0, h2⟩
  have hpt : (axisElt hj₁ hj₂ ^ 2) •
        BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1
      = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂ ^ 2) := by
    rw [BassSerreHNN.smul_vmk, mul_one]
  have h2' : k • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ ^ 2)
      = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂ ^ 2) := by
    rw [← hpt]
    exact h2
  exact Set.mem_singleton_iff.2
    (eq_one_of_fixes_axis_ends hj₁ hj₂ hinter k h0 h2')

/-- **`u₂u₁⁻¹` is a WPD element for the Bass--Serre action of `E`**, with no
hypothesis beyond `Δ₁ ∩ Δ₂ = 1`.  Minasyan--Osin's Corollary 4.3 is applied at
`ℓ = 1` and `N = 2`. -/
theorem isWPDAt_axisElt_unconditional (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1) :
    IsWPDAt (axisElt hj₁ hj₂)
      (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1) :=
  isWPDAt_of_axis_pairStab_finite
    (BassSerreHNN.tree_isTree (stageTwoEquiv j₁ j₂ hj₁ hj₂))
    (BassSerreHNN.graph_dist_smul (stageTwoEquiv j₁ j₂ hj₁ hj₂))
    (ℓ := 1) (N := 2) Nat.one_pos (dist_vmk_axisElt_pow hj₁ hj₂)
    (pairStab_axis_vertex_finite hj₁ hj₂ hinter)

/-- **`GGT.SkeletonAH3Input`, proved.**  For every `P`, `S` and every injective
`f : P × P × S →* P`, the group `E` acts on the Bass--Serre tree of its second
HNN splitting --- a `0`-hyperbolic space --- with `u₂u₁⁻¹` loxodromic and WPD.
So the `(AH₃)` datum of `E` is no longer a hypothesis anywhere. -/
theorem skeletonAH3Input_unconditional : SkeletonAH3Input.{0} := by
  intro P S instP instS f hf
  exact ⟨ah3DataOfWPD (factorOne_injective f hf) (factorTwo_injective f hf)
    (isWPDAt_axisElt_unconditional (factorOne_injective f hf)
      (factorTwo_injective f hf) (skeleton_inter f hf))⟩

/-- **The manuscript's Minasyan--Osin citation, reduced to Osin's Theorem 1.2
alone.**  The tree half is proved; `(AH₃) ⇒ (AH₁)` is what is left. -/
theorem minasyanOsinStatement_of_osinTheorem12 (hOsin : OsinTheorem12.{0, 0}) :
    MinasyanOsinStatement :=
  minasyanOsinStatement_of hOsin skeletonAH3Input_unconditional

/-- `E` is acylindrically hyperbolic, on Osin's Theorem 1.2 and nothing else. -/
theorem skeleton_isAcylindricallyHyperbolic_of_osin {Q R : Type} [Group Q]
    [Group R] (f : (Q × Q × R) →* Q) (hf : Function.Injective f)
    (hOsin : OsinTheorem12.{0, 0}) :
    IsAcylindricallyHyperbolic (Skeleton f hf) :=
  minasyanOsinStatement_of_osinTheorem12 hOsin Q R inferInstance inferInstance f hf

end BassSerreDoubleHNN

end GGT
end GroupApproximation
