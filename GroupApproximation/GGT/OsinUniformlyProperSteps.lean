import GroupApproximation.GGT.OsinQuasiFixedProduct
import GroupApproximation.GGT.PNaiveShadow
import GroupApproximation.GGT.PNaiveTransversal

/-!
# The pointwise steps of Ivanov--Olshanskii's lemma (Osin 2016, Lemma 3.4)

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), Lemma 3.4
(Ivanov--Olshanskii):

> A uniformly proper action on a hyperbolic space cannot be parabolic.  That is,
> if `G` is a group acting on a hyperbolic space uniformly properly with unbounded
> orbits, then `G` contains a loxodromic element.

Osin's proof has two loxodromy criteria and one displacement estimate, all
local at a point `x`.  This module proves them with the four-point constant;
the counting argument that consumes them is `GGT/OsinUniformlyProper`.

* **(6)** If `2 (g x | g⁻¹ x)_x + K ≤ d(x, g x)` with `K > 2δ`, then `g` is
  loxodromic (`isLoxodromic_of_small_turn`).
* **(7) ⇒ (8)** If both `g` and `h` have turns larger than their displacement
  minus `K`, and `2 (g x | h x)_x + K + 4δ ≤ min{d(x, g x), d(x, h x)}`, then
  `2 (g⁻¹ x | h⁻¹ x)_x + K ≤ min{…}` (`two_mul_gromovProduct_inv_le`).
* **(8) ⇒ loxodromic** If both products are small, then `g⁻¹ h` is loxodromic,
  through the chain `x, g⁻¹ x, g⁻¹ h x, g⁻¹ h g⁻¹ x, …` and Lemma 2.1
  (`isLoxodromic_inv_mul_of_small_products`).
* **(13)** If `(g x | h^{±1} x)_x ≥ t₀` and `d(x, h x) ≥ 2t₀`, the point `y` at
  distance `t₀` from `x` on a geodesic `[x, g x]` satisfies
  `d(y, h y) ≤ d(x, h x) − 2t₀ + 8δ` (`dist_smul_geodesicPoint_le`).

## Manuscript status

Infrastructure for Osin's Theorem 1.1 (the limit-set spelling of acylindrical
hyperbolicity used in `sec:torsion-free`); certifies no printed sentence on its
own.
-/

namespace GroupApproximation
namespace GGT
namespace OsinClassification

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **Osin's criterion (6).**  A turn smaller than half the displacement, by a
margin `K > 2δ`, makes the element loxodromic. -/
theorem isLoxodromic_of_small_turn {δ K : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) (hK : 2 * δ < K) {g : G} {x : X}
    (hturn : 2 * gromovProduct (g • x) (g⁻¹ • x) x + K ≤ dist x (g • x)) :
    IsLoxodromic g x := by
  have hδ0 := nonneg_delta hδ x
  have hC0 := gromovProduct_nonneg (g • x) (g⁻¹ • x) x
  exact isLoxodromic_of_local_backtracking hδ hiso
    (C := gromovProduct (g • x) (g⁻¹ • x) x) (by linarith) (by linarith)
    (PNaive.gromovProduct_turn_eq hiso g x).symm.le

/-- **Osin's step (7) ⇒ (8).**  Large turns of `g` and `h` together with a small
product `(g x | h x)_x` force a small product `(g⁻¹ x | h⁻¹ x)_x`. -/
theorem two_mul_gromovProduct_inv_le {δ K : ℝ} (hδ : IsHyperbolicSpace δ X)
    {g h : G} {x : X}
    (hg : dist x (g • x) - K < 2 * gromovProduct (g • x) (g⁻¹ • x) x)
    (hh : dist x (h • x) - K < 2 * gromovProduct (h • x) (h⁻¹ • x) x)
    (hsmall : 2 * gromovProduct (g • x) (h • x) x + (K + 4 * δ) ≤
      min (dist x (g • x)) (dist x (h • x))) :
    2 * gromovProduct (g⁻¹ • x) (h⁻¹ • x) x + K ≤
      min (dist x (g • x)) (dist x (h • x)) := by
  have hδ0 := nonneg_delta hδ x
  by_contra hcon
  push Not at hcon
  have hag : min (dist x (g • x)) (dist x (h • x)) ≤ dist x (g • x) := min_le_left _ _
  have hah : min (dist x (g • x)) (dist x (h • x)) ≤ dist x (h • x) := min_le_right _ _
  have h4a := hδ x (g • x) (g⁻¹ • x) (h • x)
  have h4b := hδ x (g⁻¹ • x) (h⁻¹ • x) (h • x)
  rw [gromovProduct_comm (h⁻¹ • x) (h • x) x] at h4b
  have hmin1 : (min (dist x (g • x)) (dist x (h • x)) - K) / 2 <
      min (gromovProduct (g⁻¹ • x) (h⁻¹ • x) x) (gromovProduct (h • x) (h⁻¹ • x) x) :=
    lt_min (by linarith) (by linarith)
  have hQ : (min (dist x (g • x)) (dist x (h • x)) - K) / 2 - δ <
      gromovProduct (g⁻¹ • x) (h • x) x := by linarith
  have hmin2 : (min (dist x (g • x)) (dist x (h • x)) - K) / 2 - δ <
      min (gromovProduct (g • x) (g⁻¹ • x) x) (gromovProduct (g⁻¹ • x) (h • x) x) :=
    lt_min (by linarith) hQ
  linarith

/-- **Osin's criterion (8).**  If the products `(g x | h x)_x` and
`(g⁻¹ x | h⁻¹ x)_x` are both smaller than half the smaller displacement, by a
margin `K > 2δ`, then `g⁻¹ h` is loxodromic. -/
theorem isLoxodromic_inv_mul_of_small_products {δ K : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) (hK : 2 * δ < K) {g h : G} {x : X}
    (h1 : 2 * gromovProduct (g • x) (h • x) x + K ≤
      min (dist x (g • x)) (dist x (h • x)))
    (h2 : 2 * gromovProduct (g⁻¹ • x) (h⁻¹ • x) x + K ≤
      min (dist x (g • x)) (dist x (h • x))) :
    IsLoxodromic (g⁻¹ * h) x := by
  -- the chain `x, g⁻¹ x, (g⁻¹ h) x, (g⁻¹ h) g⁻¹ x, …`
  let z : ℕ → X := fun n => ((g⁻¹ * h) ^ (n / 2)) • (if n % 2 = 0 then x else g⁻¹ • x)
  have hper : ∀ n : ℕ, z (n + 2) = (g⁻¹ * h) • z n := by
    intro n
    have hdiv : (n + 2) / 2 = n / 2 + 1 := Nat.add_div_right n (by norm_num)
    have hmod : (n + 2) % 2 = n % 2 := Nat.add_mod_right n 2
    show ((g⁻¹ * h) ^ ((n + 2) / 2)) • (if (n + 2) % 2 = 0 then x else g⁻¹ • x) =
      (g⁻¹ * h) • (((g⁻¹ * h) ^ (n / 2)) • (if n % 2 = 0 then x else g⁻¹ • x))
    rw [hdiv, hmod, pow_succ', mul_smul]
  have hz0 : z 0 = x := by simp [z]
  have hz1 : z 1 = g⁻¹ • x := by simp [z]
  have hz2 : z 2 = (g⁻¹ * h) • x := by
    show z (0 + 2) = (g⁻¹ * h) • x
    rw [hper 0, hz0]
  have hz3 : z 3 = (g⁻¹ * h) • g⁻¹ • x := by
    show z (1 + 2) = (g⁻¹ * h) • g⁻¹ • x
    rw [hper 1, hz1]
  -- the edges
  have hd01 : dist x (g⁻¹ • x) = dist x (g • x) := PNaive.dist_inv_smul hiso g x
  have hd12 : dist (g⁻¹ • x) ((g⁻¹ * h) • x) = dist x (h • x) := by
    rw [mul_smul, hiso]
  have hd23 : dist ((g⁻¹ * h) • x) ((g⁻¹ * h) • g⁻¹ • x) = dist x (g • x) := by
    rw [hiso, hd01]
  -- the turns, translated back to `x`
  have hp1 : gromovProduct x ((g⁻¹ * h) • x) (g⁻¹ • x) =
      gromovProduct (g • x) (h • x) x := by
    have e := gromovProduct_smul hiso g⁻¹ (g • x) (h • x) x
    rw [inv_smul_smul, smul_smul] at e
    exact e
  have hp2 : gromovProduct (g⁻¹ • x) ((g⁻¹ * h) • g⁻¹ • x) ((g⁻¹ * h) • x) =
      gromovProduct (g⁻¹ • x) (h⁻¹ • x) x := by
    have e := gromovProduct_smul hiso (g⁻¹ * h) (h⁻¹ • x) (g⁻¹ • x) x
    have e1 : (g⁻¹ * h) • h⁻¹ • x = g⁻¹ • x := by
      rw [smul_smul, mul_inv_cancel_right]
    rw [e1] at e
    rw [e, gromovProduct_comm]
  have h0 : 2 * gromovProduct (z 0) (z 2) (z 1) + K ≤ dist (z 0) (z 1) ∧
      2 * gromovProduct (z 0) (z 2) (z 1) + K ≤ dist (z 1) (z 2) := by
    rw [hz0, hz1, hz2, hp1, hd01, hd12]
    exact ⟨le_trans h1 (min_le_left _ _), le_trans h1 (min_le_right _ _)⟩
  have h1' : 2 * gromovProduct (z 1) (z 3) (z 2) + K ≤ dist (z 1) (z 2) ∧
      2 * gromovProduct (z 1) (z 3) (z 2) + K ≤ dist (z 2) (z 3) := by
    rw [hz1, hz2, hz3, hp2, hd12, hd23]
    exact ⟨le_trans h2 (min_le_right _ _), le_trans h2 (min_le_left _ _)⟩
  have hturns := chain_turns_of_two_periodic hiso z hper h0 h1'
  have hlox := isLoxodromic_of_periodic_chain hδ hK z (p := 2) (by norm_num) hper
    (fun n => (hturns n).1) (fun n => (hturns n).2)
  rwa [hz0] at hlox

/-- **Osin's displacement estimate (13).**  Let `y` be the point at distance `t₀`
from `x` on a geodesic `[x, g x]`.  If `h x` and `h⁻¹ x` are both seen from `x` in
the direction of `g x` up to `t₀`, and `d(x, h x) ≥ 2 t₀`, then `h` moves `y` by at
most `d(x, h x) − 2 t₀ + 8δ`. -/
theorem dist_smul_geodesicPoint_le {δ t₀ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    {g h : G} {x : X} {p : ℝ → X} (hp : IsGeodesicSegment p 0 (dist x (g • x)))
    (hp0 : p 0 = x) (hp1 : p (dist x (g • x)) = g • x) (ht0 : 0 ≤ t₀)
    (htg : t₀ ≤ dist x (g • x)) (hth : 2 * t₀ ≤ dist x (h • x))
    (hprod1 : t₀ ≤ gromovProduct (g • x) (h • x) x)
    (hprod2 : t₀ ≤ gromovProduct (g • x) (h⁻¹ • x) x) :
    dist (p t₀) (h • p t₀) ≤ dist x (h • x) - 2 * t₀ + 8 * δ := by
  have hL : dist x (h⁻¹ • x) = dist x (h • x) := PNaive.dist_inv_smul hiso h x
  obtain ⟨q, hq, hq0, hq1⟩ := hgeo x (h⁻¹ • x)
  -- `r = h · [h⁻¹ x, x]`, a geodesic from `x` to `h x`
  have hrgeo : IsGeodesicSegment (fun s => h • q (dist x (h⁻¹ • x) - s)) 0
      (dist x (h • x)) := by
    rw [← hL]
    exact hq.reverse.smul hiso h
  have hr0 : (fun s => h • q (dist x (h⁻¹ • x) - s)) 0 = x := by
    show h • q (dist x (h⁻¹ • x) - 0) = x
    rw [sub_zero, hq1, smul_inv_smul]
  have hr1 : (fun s => h • q (dist x (h⁻¹ • x) - s)) (dist x (h • x)) = h • x := by
    show h • q (dist x (h⁻¹ • x) - dist x (h • x)) = h • x
    rw [hL, sub_self, hq0]
  -- `y` is `4δ`-close to the points at distance `t₀` on `[x, h⁻¹ x]` and on `[x, h x]`
  have hstepA : dist (p t₀) (q t₀) ≤ 4 * δ :=
    dist_le_four_delta_of_le_gromovProduct hδ hδ0 hp hp0 hp1 hq hq0 hq1 ht0 htg
      (by rw [hL]; linarith) hprod2
  have hstepB : dist (p t₀) (h • q (dist x (h⁻¹ • x) - t₀)) ≤ 4 * δ :=
    dist_le_four_delta_of_le_gromovProduct hδ hδ0 hp hp0 hp1 hrgeo hr0 hr1 ht0 htg
      (by linarith) hprod1
  -- the two points of `[x, h x]` at distances `t₀` from either end
  have hstepC : dist (h • q (dist x (h⁻¹ • x) - t₀)) (h • q t₀) =
      dist x (h • x) - 2 * t₀ := by
    have hmem1 : t₀ ∈ Set.Icc (0 : ℝ) (dist x (h • x)) := ⟨ht0, by linarith⟩
    have hmem2 : dist x (h • x) - t₀ ∈ Set.Icc (0 : ℝ) (dist x (h • x)) :=
      ⟨by linarith, by linarith⟩
    have h1 := hrgeo t₀ hmem1 (dist x (h • x) - t₀) hmem2
    have harg : dist x (h⁻¹ • x) - (dist x (h • x) - t₀) = t₀ := by
      rw [hL]
      ring
    simp only [harg] at h1
    rw [h1, abs_of_nonpos (by linarith)]
    ring
  have hstepD : dist (h • q t₀) (h • p t₀) ≤ 4 * δ := by
    rw [hiso h, dist_comm]
    exact hstepA
  have htri1 := dist_triangle (p t₀) (h • q (dist x (h⁻¹ • x) - t₀)) (h • p t₀)
  have htri2 := dist_triangle (h • q (dist x (h⁻¹ • x) - t₀)) (h • q t₀) (h • p t₀)
  linarith

end OsinClassification
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinClassification.isLoxodromic_of_small_turn
#audit_axioms GroupApproximation.GGT.OsinClassification.two_mul_gromovProduct_inv_le
#audit_axioms GroupApproximation.GGT.OsinClassification.isLoxodromic_inv_mul_of_small_products
#audit_axioms GroupApproximation.GGT.OsinClassification.dist_smul_geodesicPoint_le
