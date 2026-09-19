import GroupApproximation.Sofic.InvolutionCollapseIndexCapture

/-!
# Endpoint preparation for the involution collapse

Support lemmas consumed by the collapse endpoint:

* limiting squared seminorms only depend on the eventual values of a
  bounded sequence;
* microstates of orbit-fixed movers eventually vanish exactly (the
  rigidity of commuting exact involutions in action);
* limiting smallness transfers to stagewise smallness on a
  hyperfilter-large set of stages;
* the mixed conjugation defect for a one-sided compressor: microstates of
  `ι(a) s⁻¹` and `s⁻¹ ι(δₐ)` agree asymptotically when
  `s ι(a) s⁻¹ = ι(δₐ)`.
-/

namespace GroupApproximation
namespace InvolutionCollapseEndpointPrep

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile InvolutionCollapseCocycle
open InvolutionCollapseCenter
open Ultralimit KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]

/-- Microstates of an orbit-fixed mover eventually vanish exactly. -/
theorem eventually_bVec_eq_zero_of_orbit_fixed
    (B : OpAlmostRepresentation E) (iota : Γ →* E) (k : E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    {δa : Γ} (hfix : orbitElement iota k δa = k) :
    ∃ N, ∀ n ≥ N, bVec B V S hgen hsymm n δa = 0 := by
  have hraw : ∀ n, raw B iota k n δa = raw B iota k n 1 := by
    intro n
    unfold raw
    rw [hfix, orbitElement_one]
  obtain ⟨N₁, hN₁⟩ := hVconv δa (1 / 2) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := hVconv 1 (1 / 2) (by norm_num)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hVeq : V n δa = V n 1 := by
    refine eq_of_norm_sub_lt_two (hVinv n δa) (hVinv n 1)
      (hVcomm n δa 1) ?_
    have h₁ := hN₁ n ((le_max_left _ _).trans hn)
    have h₂ := hN₂ n ((le_max_right _ _).trans hn)
    have hsplit : V n δa - V n 1 =
        (V n δa - raw B iota k n δa) -
          (V n 1 - raw B iota k n 1) := by
      rw [hraw n]
      abel
    calc
      ‖V n δa - V n 1‖ =
          ‖(V n δa - raw B iota k n δa) -
            (V n 1 - raw B iota k n 1)‖ := by rw [hsplit]
      _ ≤ ‖V n δa - raw B iota k n δa‖ +
          ‖V n 1 - raw B iota k n 1‖ := norm_sub_le _ _
      _ < 2 := by linarith
  unfold bVec
  split_ifs with h
  · rw [hVeq, sub_self, flatE_zero, smul_zero]
  · rfl

/-- Limiting smallness gives stagewise smallness on a hyperfilter-large
set of stages. -/
theorem eventually_norm_le_of_seqNormSq_le {H : ℕ → Type*}
    [∀ n, NormedAddCommGroup (H n)] {v : ∀ n, H n}
    (hb : IsBoundedSeq v) {d : ℝ} (hd : seqNormSq v ≤ d)
    (hdpos : 0 < d) :
    ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ‖v n‖ ≤ Real.sqrt (2 * d) := by
  have hlt : seqNorm v < Real.sqrt (2 * d) := by
    have hsq : seqNorm v ^ 2 ≤ d := by
      rw [← seqNormSq_eq_sq hb]
      exact hd
    have hnn : 0 ≤ seqNorm v := seqNorm_nonneg hb
    have hs : Real.sqrt (2 * d) ^ 2 = 2 * d :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (2 * d)]
  filter_upwards [eventually_norm_lt_of_seqNorm_lt hb hlt] with n hn
  exact hn.le

/-- The mixed conjugation defect: when `s ι(a) s⁻¹ = ι(δₐ)`, the
microstates of `ι(a)` and the compressor satisfy the corresponding
intertwining asymptotically. -/
theorem mixed_conj_defect_vanishing
    (B : OpAlmostRepresentation E) (iota : Γ →* E) (s : E) {a δa : Γ}
    (hda : s * iota a * s⁻¹ = iota δa) :
    OpNormVanishing B (fun n ↦
      (B.map n (iota a) : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        (B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          B.map n (iota δa)) := by
  have hgrp : iota a * s⁻¹ = s⁻¹ * iota δa := by
    rw [← hda]
    group
  have hnorm : ∀ (g : E) (n : ℕ),
      ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 :=
    fun g n ↦ norm_le_one_of_mem_unitary (B.map n g).2
  -- U_a (U_sᴴ − U_{s⁻¹})
  have h₁ : OpNormVanishing B (fun n ↦
      (B.map n (iota a) : Matrix (B.model n) (B.model n) ℂ) *
        ((B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ -
          B.map n s⁻¹)) := by
    have h := (map_inv_vanishing B s).neg
    have := h.mul_left_of_norm_le_one
      (fun n ↦ (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ)) (hnorm (iota a))
    exact this.congr fun n ↦ by noncomm_ring
  -- U_a U_{s⁻¹} − U_{a s⁻¹}
  have h₂ : OpNormVanishing B (fun n ↦
      (B.map n (iota a) : Matrix (B.model n) (B.model n) ℂ) *
        B.map n s⁻¹ - B.map n (iota a * s⁻¹)) :=
    (multiplicativeDefect_vanishing B (iota a) s⁻¹).neg.congr
      fun n ↦ by rw [neg_sub]
  -- U_{s⁻¹ δa} − U_{s⁻¹} U_{δa}
  have h₃ : OpNormVanishing B (fun n ↦
      (B.map n (s⁻¹ * iota δa) : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n s⁻¹ : Matrix (B.model n) (B.model n) ℂ) *
          B.map n (iota δa)) :=
    multiplicativeDefect_vanishing B s⁻¹ (iota δa)
  -- (U_{s⁻¹} − U_sᴴ) U_{δa}
  have h₄ : OpNormVanishing B (fun n ↦
      ((B.map n s⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
        B.map n (iota δa)) :=
    (map_inv_vanishing B s).mul_right_of_norm_le_one
      (fun n ↦ (B.map n (iota δa) :
        Matrix (B.model n) (B.model n) ℂ)) (hnorm (iota δa))
  refine (((h₁.add h₂).add h₃).add h₄).congr fun n ↦ ?_
  rw [hgrp]
  noncomm_ring

end InvolutionCollapseEndpointPrep
end GroupApproximation
