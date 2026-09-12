import GroupApproximation.GGT.OsinLinealExclusion
import GroupApproximation.GGT.AcylindricallyHyperbolicOsin

/-!
# Two spellings of non-elementarity agree for acylindrical actions

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), §1: "a group `G` is
called acylindrically hyperbolic if it admits a non-elementary acylindrical
action on a hyperbolic space", with non-elementarity meaning `|Λ(G)| > 2`.
Osin adds: "If the action is acylindrical, non-elementarity is equivalent to
condition (c) from Theorem 1.1", that is, `G` contains infinitely many
independent loxodromic elements.

This module proves the equivalence for the two spellings in the repository.

* The limit-set spelling is `SequentialBoundary.IsAcylindricallyHyperbolicLimitSet`
  (`GGT/GromovSequentialBoundary`).
* The independent-loxodromics spelling is `GGT.IsAcylindricallyHyperbolicOsin`
  (`GGT/AcylindricallyHyperbolicOsin`), which in turn is equivalent to Hull's
  Cayley-graph notion `IsAcylindricallyHyperbolic`.

The result is `isAcylindricallyHyperbolicLimitSet_iff`.

* Limit set ⇒ loxodromics is `actsNonElementarily_of_limitSetHasMoreThanTwoPoints`
  (`GGT/OsinLinealExclusion`).
* Loxodromics ⇒ limit set: from independent loxodromics `g, h`, take powers with a
  local gap.  The sequences `gⁿ w`, `g⁻ⁿ w`, `hⁿ w` converge at infinity.  The two
  ends of `g` meet at `w` with a bounded product, and independence bounds the
  products between the ends of `g` and the end of `h`
  (`limitSetHasMoreThanTwoPoints_of_actsNonElementarily`).

## Manuscript status

The limit-set spelling of "acylindrically hyperbolic" in `sec:torsion-free` agrees
with the repository's notion; certifies the definitional sentence together with
the census row that cites it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinClassification

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.SequentialBoundary
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section Action

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **The positive power orbit of a local gap converges at infinity.** -/
theorem convergesAtInfinity_pow_orbit {δ C : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {w : X}
    (hloc : gromovProduct (h • w) (h⁻¹ • w) w ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist w (h • w)) :
    ConvergesAtInfinity (fun i : ℕ => (h ^ (i + 1)) • w) w := by
  intro M
  have hL : 0 < dist w (h • w) - 2 * (C + δ) := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((M + (C + 2 * δ)) / (dist w (h • w) - 2 * (C + δ)))
  refine ⟨N, fun i j hi hj => ?_⟩
  have hprod := le_gromovProduct_pow_pow' hδ hδ0 hiso hloc hC hgap
    (i := i + 1) (j := j + 1) (by omega) (by omega)
  have hmin : (N : ℝ) ≤ ((min (i + 1) (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast le_min (by omega) (by omega)
  rw [div_lt_iff₀ hL] at hN
  have hmul := mul_le_mul_of_nonneg_left hmin hL.le
  show M ≤ gromovProduct ((h ^ (i + 1)) • w) ((h ^ (j + 1)) • w) w
  linarith

/-- **Independent loxodromics give a limit set with more than two points.** -/
theorem limitSetHasMoreThanTwoPoints_of_actsNonElementarily {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hiso : IsIsometricAction G X) {w : X}
    (hne : ActsNonElementarily (⊤ : Subgroup G) w) :
    LimitSetHasMoreThanTwoPoints G w := by
  have hδ0 := nonneg_delta hδ w
  obtain ⟨g, -, h, -, hg, hh, Cind, hCind⟩ := hne
  obtain ⟨k, _hk, hgapg⟩ :=
    exists_power_local_backtracking_gap hiso (δ := 2 * δ) (by linarith) hg
  obtain ⟨k', _hk', hgaph⟩ :=
    exists_power_local_backtracking_gap hiso (δ := 2 * δ) (by linarith) hh
  have hlocg : gromovProduct ((g ^ k) • w) ((g ^ k)⁻¹ • w) w ≤
      gromovProduct w ((g ^ (2 * k)) • w) ((g ^ k) • w) := by
    rw [PNaive.gromovProduct_turn_eq hiso (g ^ k) w, ← pow_mul, mul_comm]
  have hloch : gromovProduct ((h ^ k') • w) ((h ^ k')⁻¹ • w) w ≤
      gromovProduct w ((h ^ (2 * k')) • w) ((h ^ k') • w) := by
    rw [PNaive.gromovProduct_turn_eq hiso (h ^ k') w, ← pow_mul, mul_comm]
  have hCg := gromovProduct_nonneg w ((g ^ (2 * k)) • w) ((g ^ k) • w)
  have hCh := gromovProduct_nonneg w ((h ^ (2 * k')) • w) ((h ^ k') • w)
  -- the inverse power has the same local gap
  have hlocg' : gromovProduct ((g ^ k)⁻¹ • w) ((g ^ k)⁻¹⁻¹ • w) w ≤
      gromovProduct w ((g ^ (2 * k)) • w) ((g ^ k) • w) := by
    rw [PNaive.gromovProduct_inv_turn]
    exact hlocg
  have hgapg' : 2 * (gromovProduct w ((g ^ (2 * k)) • w) ((g ^ k) • w) + 2 * δ) <
      dist w ((g ^ k)⁻¹ • w) := by
    rw [PNaive.dist_inv_smul hiso]
    exact hgapg
  have hpowg : ∀ i : ℕ, (g ^ k) ^ (i + 1) = g ^ (((k * (i + 1) : ℕ)) : ℤ) := fun i => by
    rw [← pow_mul, zpow_natCast]
  have hinvg : ∀ i : ℕ, ((g ^ k)⁻¹) ^ (i + 1) = g ^ (-(((k * (i + 1) : ℕ)) : ℤ)) := fun i => by
    rw [inv_pow, ← pow_mul, zpow_neg, zpow_natCast]
  have hpowh : ∀ j : ℕ, (h ^ k') ^ (j + 1) = h ^ (((k' * (j + 1) : ℕ)) : ℤ) := fun j => by
    rw [← pow_mul, zpow_natCast]
  refine ⟨fun i => (g ^ k) ^ (i + 1), fun i => ((g ^ k)⁻¹) ^ (i + 1),
    fun i => (h ^ k') ^ (i + 1),
    convergesAtInfinity_pow_orbit hδ hδ0 hiso hlocg hCg hgapg,
    convergesAtInfinity_pow_orbit hδ hδ0 hiso hlocg' hCg hgapg',
    convergesAtInfinity_pow_orbit hδ hδ0 hiso hloch hCh hgaph, ?_, ?_, ?_⟩
  · -- the two ends of `g`
    refine not_equivAtInfinity_of_bounded
      (C := gromovProduct w ((g ^ (2 * k)) • w) ((g ^ k) • w) + 2 * δ) fun i j => ?_
    have h1 := PNaive.gromovProduct_inv_pow_pow_le hδ hδ0 hiso hlocg hCg hgapg
      (i := j + 1) (j := i + 1) (by omega) (by omega)
    rw [gromovProduct_comm] at h1
    exact h1
  · -- the negative end of `g` and the end of `h`
    refine not_equivAtInfinity_of_bounded (C := Cind) fun i j => ?_
    show gromovProduct ((((g ^ k)⁻¹) ^ (i + 1)) • w) (((h ^ k') ^ (j + 1)) • w) w ≤ Cind
    rw [hinvg i, hpowh j]
    exact hCind _ _
  · -- the positive end of `g` and the end of `h`
    refine not_equivAtInfinity_of_bounded (C := Cind) fun i j => ?_
    show gromovProduct (((g ^ k) ^ (i + 1)) • w) (((h ^ k') ^ (j + 1)) • w) w ≤ Cind
    rw [hpowg i, hpowh j]
    exact hCind _ _

end Action

/-- **The limit-set spelling of acylindrical hyperbolicity is the repository's
notion.** -/
theorem isAcylindricallyHyperbolicLimitSet_iff (G : Type) [Group G] :
    IsAcylindricallyHyperbolicLimitSet G ↔ IsAcylindricallyHyperbolic G := by
  rw [isAcylindricallyHyperbolic_iff_osin]
  constructor
  · rintro ⟨X, instX, instA, hiso, hgeo, ⟨δ, hδ⟩, hacy, w, hlim⟩
    letI := instX
    letI := instA
    exact ⟨X, instX, instA, hiso, hgeo, ⟨δ, hδ⟩, hacy, w,
      actsNonElementarily_of_limitSetHasMoreThanTwoPoints hδ hgeo hiso hacy hlim⟩
  · rintro ⟨X, instX, instA, hiso, hgeo, ⟨δ, hδ⟩, hacy, w, hne⟩
    letI := instX
    letI := instA
    exact ⟨X, instX, instA, hiso, hgeo, ⟨δ, hδ⟩, hacy, w,
      limitSetHasMoreThanTwoPoints_of_actsNonElementarily hδ hiso hne⟩

/-- **The two spellings agree for every group**, as a closed statement. -/
theorem isAcylindricallyHyperbolicLimitSet_iff_all :
    ∀ (G : Type) [Group G], IsAcylindricallyHyperbolicLimitSet G ↔ IsAcylindricallyHyperbolic G :=
  fun G _ => isAcylindricallyHyperbolicLimitSet_iff G

end OsinClassification
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinClassification.convergesAtInfinity_pow_orbit
#audit_axioms GroupApproximation.GGT.OsinClassification.limitSetHasMoreThanTwoPoints_of_actsNonElementarily
#audit_axioms GroupApproximation.GGT.OsinClassification.isAcylindricallyHyperbolicLimitSet_iff
#audit_closed_axioms GroupApproximation.GGT.OsinClassification.isAcylindricallyHyperbolicLimitSet_iff_all
