import GroupApproximation.Kazhdan.KazhdanDisplacementCriterion
import GroupApproximation.Kazhdan.PositiveOperatorGap
import GroupApproximation.Kazhdan.RealGroupRing

/-!
# Exact group-ring certificates imply property (T)

This file closes the analytic bridge from an exact Ozawa-style identity

`Delta* Delta - c Delta = sum_i xi_i* xi_i`

to a genuine Kazhdan pair.  The proof uses only finite-sum estimates and the
kernel-checked positive-operator gap lemma; no spectral theorem or numerical
positivity assertion is imported.
-/

namespace GroupApproximation
namespace GroupRingSOSPropertyT

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Laplacian quadratic form is bounded above by twice the size of its
finite control set. -/
theorem laplacian_energy_le (S : Finset G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    inner ℝ x (GroupRingLaplacian.laplacian S ρ x) ≤
      (2 * S.card : ℝ) * ‖x‖ ^ 2 := by
  have hterm (g : G) (hg : g ∈ S) :
      ‖ρ g x - x‖ ^ 2 ≤ 4 * ‖x‖ ^ 2 := by
    have hnorm : ‖ρ g x - x‖ ≤ 2 * ‖x‖ := by
      calc
        ‖ρ g x - x‖ ≤ ‖ρ g x‖ + ‖x‖ := norm_sub_le _ _
        _ = 2 * ‖x‖ := by rw [(ρ g).norm_map]; ring
    nlinarith [norm_nonneg (ρ g x - x), norm_nonneg x]
  have hsum :
      ∑ g ∈ S, ‖ρ g x - x‖ ^ 2 ≤
        (S.card : ℝ) * (4 * ‖x‖ ^ 2) := by
    calc
      ∑ g ∈ S, ‖ρ g x - x‖ ^ 2 ≤
          ∑ _g ∈ S, 4 * ‖x‖ ^ 2 :=
        Finset.sum_le_sum fun g hg ↦ hterm g hg
      _ = (S.card : ℝ) * (4 * ‖x‖ ^ 2) := by simp
  have henergy := GroupRingLaplacian.two_mul_inner_laplacian S ρ x
  nlinarith

/-- The squared norm of the Laplacian is bounded by its energy times twice
the size of the finite control set. -/
theorem laplacian_norm_sq_le (S : Finset G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖GroupRingLaplacian.laplacian S ρ x‖ ^ 2 ≤
      (2 * S.card : ℝ) *
        inner ℝ x (GroupRingLaplacian.laplacian S ρ x) := by
  rw [GroupRingLaplacian.laplacian_apply]
  have htriangle :
      ‖∑ g ∈ S, (x - ρ g x)‖ ≤ ∑ g ∈ S, ‖x - ρ g x‖ :=
    norm_sum_le _ _
  have hsumNonneg : 0 ≤ ∑ g ∈ S, ‖x - ρ g x‖ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hsquare := sq_le_sq₀ (norm_nonneg _) hsumNonneg |>.2 htriangle
  have hcauchy :
      (∑ g ∈ S, ‖x - ρ g x‖) ^ 2 ≤
        (S.card : ℝ) * ∑ g ∈ S, ‖x - ρ g x‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq S
      (fun _ ↦ (1 : ℝ)) (fun g ↦ ‖x - ρ g x‖)
  have henergy := GroupRingLaplacian.two_mul_inner_laplacian S ρ x
  have hnorm (g : G) : ‖x - ρ g x‖ = ‖ρ g x - x‖ := by
    rw [show x - ρ g x = -(ρ g x - x) by abel, norm_neg]
  simp_rw [hnorm] at hcauchy
  calc
    ‖∑ g ∈ S, (x - ρ g x)‖ ^ 2 ≤
        (∑ g ∈ S, ‖x - ρ g x‖) ^ 2 := hsquare
    _ ≤ (S.card : ℝ) * ∑ g ∈ S, ‖ρ g x - x‖ ^ 2 := by
      simpa only [hnorm] using hcauchy
    _ = (2 * S.card : ℝ) *
        inner ℝ x (∑ g ∈ S, (x - ρ g x)) := by
      rw [← GroupRingLaplacian.laplacian_apply S ρ x, ← henergy]
      ring

/-- Exact algebraic self-adjointness of the Laplacian gives symmetry in
every orthogonal representation. -/
theorem laplacian_inner_comm_of_adjoint_eq
    (S : Finset G)
    (hself : RealGroupRing.adjoint (RealGroupRing.laplacianElement S) =
      RealGroupRing.laplacianElement S)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) :
    inner ℝ (GroupRingLaplacian.laplacian S ρ x) y =
      inner ℝ x (GroupRingLaplacian.laplacian S ρ y) := by
  have h := RealGroupRing.inner_evaluate_adjoint
    (RealGroupRing.laplacianElement S) ρ x y
  rw [hself, RealGroupRing.evaluate_laplacianElement,
    RealGroupRing.evaluate_laplacianElement] at h
  exact h.symm

/-- Complete exact certificate data for the Ozawa Laplacian criterion. -/
def IsKazhdanSOSCertificate (S : Finset G) (c : ℝ) : Prop :=
  0 < c ∧
    c ≤ (2 * S.card : ℝ) ∧
    Subgroup.closure (S : Set G) = ⊤ ∧
    RealGroupRing.adjoint (RealGroupRing.laplacianElement S) =
      RealGroupRing.laplacianElement S ∧
    RealGroupRing.IsSOSQuadraticGap S c

/-- **Exact SOS criterion for property `(T)`.**

An algebraically self-adjoint generating Laplacian satisfying an exact
positive Ozawa identity yields a concrete Kazhdan pair.  All analytic bounds
are derived here from the finite control set. -/
theorem hasKazhdanPropertyT_of_sosCertificate
    (S : Finset G) {c : ℝ}
    (hcert : IsKazhdanSOSCertificate S c) :
    HasKazhdanPropertyT.{u, v} G := by
  classical
  rcases hcert with ⟨hc, hcM, hgen, hself, hsos⟩
  let M : ℝ := 2 * S.card
  have hM : 0 < M := hc.trans_le hcM
  have hratioPos : 0 < c / M := div_pos hc hM
  have hratioLe : c / M ≤ 1 := (div_le_one hM).2 hcM
  have hargNonneg : 0 ≤ 1 - c / M := sub_nonneg.mpr hratioLe
  have hsqrtLt : Real.sqrt (1 - c / M) < 1 := by
    have hsqrtSq : Real.sqrt (1 - c / M) ^ 2 = 1 - c / M :=
      Real.sq_sqrt hargNonneg
    have hsqrtNonneg := Real.sqrt_nonneg (1 - c / M)
    nlinarith
  let d : ℝ := c * (1 - Real.sqrt (1 - c / M))
  have hd : 0 < d := by
    exact mul_pos hc (sub_pos.mpr hsqrtLt)
  let n : ℝ := S.card
  have hn : 0 ≤ n := by positivity
  have hn1 : 0 < n + 1 := by linarith
  let ε : ℝ := d / (2 * (n + 1))
  have hε : 0 < ε := div_pos hd (mul_pos (by norm_num) hn1)
  refine ⟨S, ε,
    IsKazhdanPair.of_noInvariant_displacement_mul_norm hε ?_⟩
  intro E _ _ _ ρ hno x hx0
  let A := GroupRingLaplacian.laplacian S ρ
  have hsymm : ∀ y z : E, inner ℝ (A y) z = inner ℝ y (A z) := by
    intro y z
    exact laplacian_inner_comm_of_adjoint_eq S hself ρ y z
  have henergy : ∀ y : E, 0 ≤ PositiveOperatorGap.energy A y := by
    intro y
    exact GroupRingLaplacian.inner_laplacian_nonneg S ρ y
  have hlower : ∀ y : E,
      c * PositiveOperatorGap.energy A y ≤ ‖A y‖ ^ 2 := by
    intro y
    exact RealGroupRing.quadratic_gap_of_sos S hsos ρ y
  have hformUpper : ∀ y : E,
      PositiveOperatorGap.energy A y ≤ M * ‖y‖ ^ 2 := by
    intro y
    exact laplacian_energy_le S ρ y
  have hnormUpper : ∀ y : E,
      ‖A y‖ ^ 2 ≤ M * PositiveOperatorGap.energy A y := by
    intro y
    exact laplacian_norm_sq_le S ρ y
  have hker : ∀ y : E, A y = 0 → y = 0 := by
    intro y hy
    apply hno y
    exact (KazhdanOrthogonal.mem_invariantSubmodule ρ y).mp
      ((GroupRingLaplacian.laplacian_apply_eq_zero_iff_invariant
        S hgen ρ y).mp hy)
  have hinverse (y : E) : ‖y‖ ≤ d⁻¹ * ‖A y‖ := by
    simpa [d, M] using
      (PositiveOperatorGap.norm_le_of_quadratic_gap
        A hc hM hcM hsymm henergy hlower hformUpper hnormUpper hker y)
  by_contra hfar
  push Not at hfar
  have hSnonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hSEmpty
    subst S
    simp [M] at hM
  have htriangle : ‖A x‖ ≤ ∑ g ∈ S, ‖ρ g x - x‖ := by
    rw [GroupRingLaplacian.laplacian_apply]
    calc
      ‖∑ g ∈ S, (x - ρ g x)‖ ≤ ∑ g ∈ S, ‖x - ρ g x‖ :=
        norm_sum_le _ _
      _ = ∑ g ∈ S, ‖ρ g x - x‖ := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [show x - ρ g x = -(ρ g x - x) by abel, norm_neg]
  have hsum : ∑ g ∈ S, ‖ρ g x - x‖ <
      ∑ _g ∈ S, ε * ‖x‖ :=
    Finset.sum_lt_sum_of_nonempty hSnonempty fun g hg ↦ hfar g hg
  have hA : ‖A x‖ < n * (ε * ‖x‖) := by
    calc
      ‖A x‖ ≤ ∑ g ∈ S, ‖ρ g x - x‖ := htriangle
      _ < ∑ _g ∈ S, ε * ‖x‖ := hsum
      _ = n * (ε * ‖x‖) := by simp [n]
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hinvPos : 0 < d⁻¹ := inv_pos.mpr hd
  have hstrict : d⁻¹ * ‖A x‖ < d⁻¹ * (n * (ε * ‖x‖)) :=
    mul_lt_mul_of_pos_left hA hinvPos
  have hcoefficient : d⁻¹ * (n * (ε * ‖x‖)) < ‖x‖ := by
    have hden : 0 < 2 * (n + 1) := mul_pos (by norm_num) hn1
    calc
      d⁻¹ * (n * (ε * ‖x‖)) =
          (n / (2 * (n + 1))) * ‖x‖ := by
        dsimp [ε]
        field_simp [ne_of_gt hd, ne_of_gt hden]
      _ < ‖x‖ := by
        have hfrac : n / (2 * (n + 1)) < 1 := by
          apply (div_lt_one hden).2
          nlinarith
        nlinarith
  exact (not_lt_of_ge (hinverse x)) (hstrict.trans hcoefficient)

end GroupRingSOSPropertyT
end GroupApproximation
