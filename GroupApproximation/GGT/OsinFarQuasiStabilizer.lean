import GroupApproximation.GGT.OsinChainLemma

/-!
# Elements moving a far point by less than the distance (Osin 2016, Lemma 3.6)

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), Lemma 3.6:

> Let `G` be a group acting acylindrically on a hyperbolic space `(S, d)`.  Then for
> any `ε > 0` there exist `R, N > 0` such that the following holds.  For any
> `x, y ∈ S` such that `d(x, y) ≥ R`, the set of elements `g ∈ G` satisfying
> `d(x, gx) ≤ ε` and `d(y, gy) ≤ d(x, y) + ε` has cardinality at most `N`.

The proof is Osin's, on a geodesic space with the four-point constant.  Put
`R₁ = max R₀ (2ε)`, where `R₀, N` are the acylindricity constants for `8δ + ε`,
and take `R = 3R₁`.  Let `m` be the point at distance `R₁` from `x` on a
geodesic `[x, y]`.  Two fellow-travelling comparisons show that an element as
above moves `m` by at most `8δ + ε`:

* at `x`, between `[x, y]` and `[x, g y]`;
* at `g y`, between `[g y, x]` and `[g y, g x]`.

A parameter comparison along `g [x, y]` completes the bound
(`dist_smul_point_le_of_far`).  Acylindricity at the pair `(x, m)` then bounds
the count (`far_quasiStabilizer_finite`).

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

/-- **The displacement estimate of Lemma 3.6.**  If `d(x, y) ≥ 3R₁`, `R₁ ≥ 2ε`,
and `g` moves `x` by at most `ε` and `y` by at most `d(x, y) + ε`, then `g` moves
the point at distance `R₁` from `x` on a geodesic `[x, y]` by at most `8δ + ε`. -/
theorem dist_smul_point_le_of_far {δ ε R₁ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    {g : G} {x y : X} {p : ℝ → X} (hp : IsGeodesicSegment p 0 (dist x y))
    (hp0 : p 0 = x) (hp1 : p (dist x y) = y) (hR₁ε : 2 * ε ≤ R₁)
    (hxy : 3 * R₁ ≤ dist x y) (hgx : dist x (g • x) ≤ ε)
    (hgy : dist y (g • y) ≤ dist x y + ε) :
    dist (p R₁) (g • p R₁) ≤ 8 * δ + ε := by
  have hε0 : 0 ≤ ε := le_trans dist_nonneg hgx
  obtain ⟨q, hq, hq0, hq1⟩ := hgeo x (g • y)
  have hgxgy : dist (g • x) (g • y) = dist x y := hiso g x y
  have hE_up : dist x (g • y) ≤ dist x y + ε := by
    have h := dist_triangle x (g • x) (g • y)
    rw [hgxgy] at h
    linarith
  have hE_low : dist x y - ε ≤ dist x (g • y) := by
    have h := dist_triangle (g • x) x (g • y)
    rw [hgxgy, dist_comm (g • x) x] at h
    linarith
  -- the comparison at `x`, between `[x, y]` and `[x, g y]`
  have hstep1 : dist (p R₁) (q R₁) ≤ 4 * δ := by
    refine dist_le_four_delta_of_le_gromovProduct hδ hδ0 hp hp0 hp1 hq hq0 hq1
      ?_ ?_ ?_ ?_
    · linarith
    · linarith
    · linarith
    · have hyx : dist y x = dist x y := dist_comm y x
      have hgyx : dist (g • y) x = dist x (g • y) := dist_comm (g • y) x
      simp only [gromovProduct, hyx, hgyx]
      linarith
  -- the reversed geodesics out of `g y`
  have hEx : dist (g • y) x = dist x (g • y) := dist_comm _ _
  have hDB : dist (g • y) (g • x) = dist x y := by
    rw [hiso g y x, dist_comm y x]
  have hq'geo : IsGeodesicSegment (fun t => q (dist x (g • y) - t)) 0
      (dist (g • y) x) := by
    rw [hEx]
    exact hq.reverse
  have hq'0 : (fun t => q (dist x (g • y) - t)) 0 = g • y := by
    show q (dist x (g • y) - 0) = g • y
    rw [sub_zero, hq1]
  have hq'1 : (fun t => q (dist x (g • y) - t)) (dist (g • y) x) = x := by
    show q (dist x (g • y) - dist (g • y) x) = x
    rw [hEx, sub_self, hq0]
  have hgp : IsGeodesicSegment (fun t => g • p t) 0 (dist x y) := hp.smul hiso g
  have hr'geo : IsGeodesicSegment (fun t => g • p (dist x y - t)) 0
      (dist (g • y) (g • x)) := by
    rw [hDB]
    exact hgp.reverse
  have hr'0 : (fun t => g • p (dist x y - t)) 0 = g • y := by
    show g • p (dist x y - 0) = g • y
    rw [sub_zero, hp1]
  have hr'1 : (fun t => g • p (dist x y - t)) (dist (g • y) (g • x)) = g • x := by
    show g • p (dist x y - dist (g • y) (g • x)) = g • x
    rw [hDB, sub_self, hp0]
  -- the comparison at `g y`, between `[g y, x]` and `[g y, g x]`
  have hstep2 : dist (q (dist x (g • y) - (dist x (g • y) - R₁)))
      (g • p (dist x y - (dist x (g • y) - R₁))) ≤ 4 * δ := by
    refine dist_le_four_delta_of_le_gromovProduct hδ hδ0 hq'geo hq'0 hq'1
      hr'geo hr'0 hr'1 ?_ ?_ ?_ ?_
    · linarith
    · rw [hEx]
      linarith
    · rw [hDB]
      linarith
    · simp only [gromovProduct, hgxgy]
      linarith
  have harg : dist x (g • y) - (dist x (g • y) - R₁) = R₁ := by ring
  rw [harg] at hstep2
  -- the parameter comparison along `g [x, y]`
  have hstep3 : dist (g • p (dist x y - (dist x (g • y) - R₁))) (g • p R₁) ≤ ε := by
    rw [hiso g, hp (dist x y - (dist x (g • y) - R₁)) ⟨by linarith, by linarith⟩
      R₁ ⟨by linarith, by linarith⟩, abs_le]
    constructor <;> linarith
  have htri1 := dist_triangle (p R₁) (q R₁) (g • p R₁)
  have htri2 := dist_triangle (q R₁) (g • p (dist x y - (dist x (g • y) - R₁)))
    (g • p R₁)
  linarith

/-- **Osin's Lemma 3.6.**  For an acylindrical isometric action on a geodesic
hyperbolic space and any `ε > 0`, there are `R` and `N` such that whenever
`d(x, y) ≥ R`, at most `N` elements move `x` by at most `ε` and `y` by at most
`d(x, y) + ε`. -/
theorem far_quasiStabilizer_finite {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : ℝ) (N : ℕ), ∀ x y : X, R ≤ dist x y →
      {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ dist x y + ε}.Finite ∧
        {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ dist x y + ε}.ncard ≤ N := by
  obtain ⟨R₀, N, hR₀⟩ := hacy (8 * δ + ε) (by linarith)
  have hR₁0 : R₀ ≤ max R₀ (2 * ε) := le_max_left _ _
  have hR₁ε : 2 * ε ≤ max R₀ (2 * ε) := le_max_right _ _
  refine ⟨3 * max R₀ (2 * ε), N, ?_⟩
  intro x y hxy
  obtain ⟨p, hp, hp0, hp1⟩ := hgeo x y
  have hm : dist x (p (max R₀ (2 * ε))) = max R₀ (2 * ε) := by
    have h := hp 0 ⟨le_rfl, dist_nonneg⟩ (max R₀ (2 * ε)) ⟨by linarith, by linarith⟩
    rw [hp0] at h
    rw [h, zero_sub, abs_neg, abs_of_nonneg (by linarith)]
  have hsub : {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ dist x y + ε} ⊆
      {g : G | dist x (g • x) ≤ 8 * δ + ε ∧
        dist (p (max R₀ (2 * ε))) (g • p (max R₀ (2 * ε))) ≤ 8 * δ + ε} := by
    rintro g ⟨hgx, hgy⟩
    exact ⟨by linarith,
      dist_smul_point_le_of_far hδ hδ0 hgeo hiso hp hp0 hp1 hR₁ε hxy hgx hgy⟩
  obtain ⟨hfin, hcard⟩ := hR₀ x (p (max R₀ (2 * ε))) (by rw [hm]; exact hR₁0)
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hcard⟩

end OsinClassification
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinClassification.dist_smul_point_le_of_far
#audit_axioms GroupApproximation.GGT.OsinClassification.far_quasiStabilizer_finite
