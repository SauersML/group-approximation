import GroupApproximation.Kazhdan.KazhdanComplex
import GroupApproximation.Kazhdan.KazhdanControl

/-!
# Using real Kazhdan-subset estimates in complex representations

The root estimates in `PropertyT` were proved for real Hilbert spaces.  This
file realifies a complex unitary representation and packages the homogeneous
rescaling needed when the controlled vector is not normalized.
-/

namespace GroupApproximation

open scoped InnerProductSpace

universe u w v

variable {K : Type u} [Group K]
variable {G : Type w} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A real `ControlsSubsetDisplacement` estimate applies, after composition
with any group homomorphism, to arbitrary vectors in a complex unitary
representation.  The harmless `+1` converts non-strict input bounds to the
strict inequalities in the definition. -/
theorem ControlsSubsetDisplacement.norm_comp_sub_le
    {S : Finset K} {U : Set K} {C B : ℝ}
    (hcontrol : ControlsSubsetDisplacement.{u, v} K S U C)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (f : K →* G) (rho : G →* (E ≃ₗᵢ[ℂ] E)) (z : E)
    (hnear : ∀ s ∈ S, ‖rho (f s) z - z‖ ≤ B)
    (g : K) (hg : g ∈ U) :
    ‖rho (f g) z - z‖ ≤ C * (B + 1) := by
  by_cases hz : z = 0
  · simpa [hz] using mul_nonneg hC (by linarith : 0 ≤ B + 1)
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let z₀ : E := (‖z‖⁻¹ : ℂ) • z
  have hz₀ : ‖z₀‖ = 1 := by
    rw [show ‖z₀‖ = ‖(‖z‖⁻¹ : ℂ)‖ * ‖z‖ by simp [z₀, norm_smul]]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg z), inv_mul_cancel₀ hn.ne']
  let delta : ℝ := (B + 1) / ‖z‖
  have hdelta : 0 < delta := div_pos (by linarith) hn
  have hnear₀ : ∀ s ∈ S, ‖rho (f s) z₀ - z₀‖ < delta := by
    intro s hs
    have hsB := hnear s hs
    have heq : rho (f s) z₀ - z₀ =
        (‖z‖⁻¹ : ℂ) • (rho (f s) z - z) := by
      simp [z₀, smul_sub]
    rw [heq, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    dsimp [delta]
    rw [div_eq_mul_inv]
    simpa [mul_comm] using
      (mul_lt_mul_of_pos_right (lt_of_le_of_lt hsB (lt_add_one B))
        (inv_pos.mpr hn))
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  have hout := hcontrol E (realifyHom (rho.comp f)) z₀ hz₀
    delta hdelta hnear₀ g hg
  have hscale : ‖rho (f g) z - z‖ =
      ‖z‖ * ‖rho (f g) z₀ - z₀‖ := by
    have hzrecover : z = (‖z‖ : ℂ) • z₀ := by
      simp only [z₀, smul_smul]
      rw [show (‖z‖ : ℂ) * (‖z‖⁻¹ : ℂ) = 1 by
        exact mul_inv_cancel₀ (by exact_mod_cast hn.ne')]
      simp
    conv_lhs => rw [hzrecover]
    rw [map_smul, ← smul_sub, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  rw [hscale]
  calc
    ‖z‖ * ‖rho (f g) z₀ - z₀‖ ≤ ‖z‖ * (C * delta) :=
      mul_le_mul_of_nonneg_left hout.le (norm_nonneg z)
    _ = C * (B + 1) := by
      dsimp [delta]
      field_simp

end GroupApproximation
