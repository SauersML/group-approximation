import GroupApproximation.GGT.HullSCConeOffHeavyFellowTravel
import GroupApproximation.GGT.HullSCConeOffHeavyModelPoint

/-!
# The uniform common-power threshold from acylindricity

This module discharges `UniformCommonZpowThreshold`.  The quantitative core in
`ElementaryIndependence` first chooses a single forward-fellow-travel threshold
from numeric loxodromy and displacement bounds.  The endpoint quadrilateral
estimate turns close orbit endpoints into that fellow travel.  The same
threshold works for the four sign combinations because inverse powers have the
same displacement data.

The input numbers are normalised with `max _ 0`.  This is necessary because the
predicate deliberately does not ask callers for redundant nonnegativity
hypotheses; replacing an upper or additive bound by its maximum with zero only
weakens the corresponding hypotheses.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- A natural power and the corresponding power of the inverse move a
basepoint the same distance. -/
theorem dist_inv_pow_smul_eq (hiso : IsIsometricAction G X) (c : G) (z : X)
    (n : ℕ) :
    dist z (((c⁻¹) ^ n) • z) = dist z ((c ^ n) • z) := by
  calc
    dist z (((c⁻¹) ^ n) • z) =
        dist ((c ^ n) • z) ((c ^ n) • (((c⁻¹) ^ n) • z)) :=
      (hiso (c ^ n) z (((c⁻¹) ^ n) • z)).symm
    _ = dist ((c ^ n) • z) z := by
      rw [inv_pow, ← mul_smul]
      simp
    _ = dist z ((c ^ n) • z) := dist_comm _ _

/-- **Acylindricity supplies the uniform threshold used by cone-off B2.** -/
theorem uniformCommonZpowThreshold_of_acylindrical {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) :
    UniformCommonZpowThreshold G X := by
  intro E la Ba Da lb Bb Db hla hlb
  let E₀ : ℝ := max E 0
  let Ba₀ : ℝ := max Ba 0
  let Da₀ : ℝ := max Da 0
  let Bb₀ : ℝ := max Bb 0
  let Db₀ : ℝ := max Db 0
  let C : ℝ := 2 * (E₀ + 6 * δ)
  have hE₀0 : 0 ≤ E₀ := by simp [E₀]
  have hBa₀0 : 0 ≤ Ba₀ := by simp [Ba₀]
  have hDa₀0 : 0 ≤ Da₀ := by simp [Da₀]
  have hBb₀0 : 0 ≤ Bb₀ := by simp [Bb₀]
  have hDb₀0 : 0 ≤ Db₀ := by simp [Db₀]
  have hC0 : 0 ≤ C := by dsimp [C]; linarith
  obtain ⟨T, -, hlong⟩ :=
    ElementaryMorse.exists_common_zpow_of_forward_fellow_travel_of_uniform_data
      hδ hδ0 hgeo hiso hacy hC0 hla hBa₀0 hDa₀0 hlb hBb₀0 hDb₀0
  refine ⟨T, ?_⟩
  intro a b z hlox_a hdisp_a hlox_b hdisp_b
  have hBa : Ba ≤ Ba₀ := le_max_left _ _
  have hDa : Da ≤ Da₀ := le_max_left _ _
  have hBb : Bb ≤ Bb₀ := le_max_left _ _
  have hDb : Db ≤ Db₀ := le_max_left _ _
  have hE : E ≤ E₀ := le_max_left _ _
  have hlox_a₀ : ∀ n : ℕ, la * n - Ba₀ ≤ dist z ((a ^ n) • z) := by
    intro n
    linarith [hlox_a n]
  have hlox_b₀ : ∀ n : ℕ, lb * n - Bb₀ ≤ dist z ((b ^ n) • z) := by
    intro n
    linarith [hlox_b n]
  have hdisp_a₀ : dist z (a • z) ≤ Da₀ := hdisp_a.trans hDa
  have hdisp_b₀ : dist z (b • z) ≤ Db₀ := hdisp_b.trans hDb
  have hlox_ai₀ : ∀ n : ℕ, la * n - Ba₀ ≤ dist z (((a⁻¹) ^ n) • z) := by
    intro n
    rw [dist_inv_pow_smul_eq hiso]
    exact hlox_a₀ n
  have hlox_bi₀ : ∀ n : ℕ, lb * n - Bb₀ ≤ dist z (((b⁻¹) ^ n) • z) := by
    intro n
    rw [dist_inv_pow_smul_eq hiso]
    exact hlox_b₀ n
  have hdisp_ai₀ : dist z (a⁻¹ • z) ≤ Da₀ := by
    simpa using (show dist z (((a⁻¹) ^ 1) • z) ≤ Da₀ by
      rw [dist_inv_pow_smul_eq hiso]
      simpa using hdisp_a₀)
  have hdisp_bi₀ : dist z (b⁻¹ • z) ≤ Db₀ := by
    simpa using (show dist z (((b⁻¹) ^ 1) • z) ≤ Db₀ by
      rw [dist_inv_pow_smul_eq hiso]
      simpa using hdisp_b₀)
  have hnat : ∀ (c d : G),
      (∀ n : ℕ, la * n - Ba₀ ≤ dist z ((c ^ n) • z)) →
      dist z (c • z) ≤ Da₀ →
      (∀ n : ℕ, lb * n - Bb₀ ≤ dist z ((d ^ n) • z)) →
      dist z (d • z) ≤ Db₀ →
      ∀ n m : ℕ,
        T ≤ dist z ((c ^ n) • z) → T ≤ dist z ((d ^ m) • z) →
        dist ((c ^ n) • z) ((d ^ m) • z) ≤ E₀ →
        ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ c ^ p = d ^ r := by
    intro c d hc hdc hd hdd n m hn hm hend
    obtain ⟨f, hf, hf0, hf1⟩ := hgeo z ((c ^ n) • z)
    obtain ⟨q, hq, hq0, hq1⟩ := hgeo z ((d ^ m) • z)
    refine hlong c d z hc hdc hd hdd n m f q hf hf0 hf1 hq hq0 hq1 hn hm ?_
    intro t ht0 htT
    refine dist_same_parameter_le_of_geodesic_close_endpoints (E := E₀)
      hδ hδ0 hgeo hE₀0 hf dist_nonneg hq dist_nonneg ?_ ?_
        ⟨ht0, htT.trans hn⟩ ⟨ht0, htT.trans hm⟩
    · rw [hf0, hq0]
    · rw [hf1, hq1]
      exact hend
  intro n m hn hm hend
  have hend₀ : dist ((a ^ n) • z) ((b ^ m) • z) ≤ E₀ := hend.trans hE
  rcases ElementaryMorse.zpow_eq_pow_toNat_or_inv a n with ⟨-, hna⟩ | ⟨-, hna⟩ <;>
    rcases ElementaryMorse.zpow_eq_pow_toNat_or_inv b m with ⟨-, hmb⟩ | ⟨-, hmb⟩ <;>
      rw [hna] at hn hend₀ <;> rw [hmb] at hm hend₀
  · exact hnat a b hlox_a₀ hdisp_a₀ hlox_b₀ hdisp_b₀ _ _ hn hm hend₀
  · exact common_zpow_of_inv_right
      (hnat a b⁻¹ hlox_a₀ hdisp_a₀ hlox_bi₀ hdisp_bi₀ _ _ hn hm hend₀)
  · exact common_zpow_of_inv_left
      (hnat a⁻¹ b hlox_ai₀ hdisp_ai₀ hlox_b₀ hdisp_b₀ _ _ hn hm hend₀)
  · exact common_zpow_of_inv_left (common_zpow_of_inv_right
      (hnat a⁻¹ b⁻¹ hlox_ai₀ hdisp_ai₀ hlox_bi₀ hdisp_bi₀ _ _ hn hm hend₀))

end HullSC
end GroupApproximation
