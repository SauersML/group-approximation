import GroupApproximation.Sofic.FinitePacketRankWeight
import GroupApproximation.Sofic.StarTranspositionRankMass
import GroupApproximation.Sofic.UltraproductScaledTransport

/-!
# The finite-packet rank contradiction

This module packages the terminal contradiction of finite-packet collapse.
For a family of braided involution displacements, the generator mass is
exactly three times the integer rank weight.  If an analytic transport
argument makes every generator displacement vanish at that same scale, the
weight is eventually zero.

The theorem is intentionally stated at the boundary supplied by scaled
Kazhdan transport.  It does not assert finite-group corona exactification or
the existence of a transported coboundary primitive; those are separate
inputs and are not hidden here.
-/

namespace GroupApproximation
namespace FinitePacketCollapseCore

open Matrix InvolutionRankMass
open FinitePacketRankWeight StarTranspositionRankMass
open ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Γ E : Type*} [Group Γ] [Group E]

/-- The real-valued version of the integer generator rank weight. -/
def packetRankWeight (B : OpAlmostRepresentation E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
    (S : Finset Γ) : ℕ → ℝ :=
  fun n ↦ (generatorRankWeight (V n) S : ℝ)

theorem packetRankWeight_nonneg (B : OpAlmostRepresentation E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
    (S : Finset Γ) :
    ∀ n, 0 ≤ packetRankWeight B V S n :=
  fun _ ↦ Nat.cast_nonneg _

/-- For braided exact involutions, total generator mass is exactly three
times the packet's integer rank weight. -/
theorem sum_generator_mass_eq_three_mul_weight
    (B : OpAlmostRepresentation E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
    (S : Finset Γ)
    (hV : ∀ n g, IsExactInvolution (V n g))
    (hbraid : ∀ n a, a ∈ S →
      V n a * V n 1 * V n a = V n 1 * V n a * V n 1)
    (n : ℕ) :
    ∑ a ∈ S, matMass (V n a - V n 1) =
      3 * packetRankWeight B V S n := by
  classical
  rw [packetRankWeight, generatorRankWeight]
  simp only [displacementRank]
  calc
    (∑ a ∈ S, matMass (V n a - V n 1)) =
        ∑ a ∈ S, 3 * (((V n a - V n 1).rank : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact matMass_sub_eq_three_mul_rank (hV n a) (hV n 1)
        (hbraid n a ha)
    _ = 3 * (∑ a ∈ S, (((V n a - V n 1).rank : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = 3 * ((∑ a ∈ S, (V n a - V n 1).rank : ℕ) : ℝ) := by
      norm_cast
    _ = 3 * ↑(∑ a ∈ S, (V n a - V n 1).rank) := rfl

/-- **Terminal finite-packet contradiction.**  If scaled transport makes all
generator displacements `o(w_n)` at their own total-rank weight, then that
integer weight is eventually zero. -/
theorem eventually_packetRankWeight_eq_zero_of_scaled_vanishing
    (B : OpAlmostRepresentation E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
    (S : Finset Γ)
    (hV : ∀ n g, IsExactInvolution (V n g))
    (hbraid : ∀ n a, a ∈ S →
      V n a * V n 1 * V n a = V n 1 * V n a * V n 1)
    (hvan : ∀ a ∈ S,
      ScaledMassVanishing B (packetRankWeight B V S)
        (fun n ↦ V n a - V n 1)) :
    ∃ N, ∀ n ≥ N, packetRankWeight B V S n = 0 := by
  classical
  let c : ℝ := (S.card : ℝ) + 1
  have hc : 0 < c := by
    dsimp [c]
    positivity
  choose N hN using fun a : ↥S ↦ hvan a.1 a.2 c⁻¹ (inv_pos.mpr hc)
  let Nmax : ℕ := S.attach.sup N
  refine ⟨Nmax, fun n hn ↦ ?_⟩
  have hterm : ∀ a ∈ S,
      matMass (V n a - V n 1) ≤ c⁻¹ * packetRankWeight B V S n := by
    intro a ha
    let aS : ↥S := ⟨a, ha⟩
    have hle : N aS ≤ Nmax := by
      exact Finset.le_sup (s := S.attach) (f := N) (Finset.mem_attach S aS)
    exact hN aS n (hle.trans hn)
  have hupper : ∑ a ∈ S, matMass (V n a - V n 1) ≤
      (S.card : ℝ) * (c⁻¹ * packetRankWeight B V S n) := by
    calc
      (∑ a ∈ S, matMass (V n a - V n 1)) ≤
          ∑ _a ∈ S, c⁻¹ * packetRankWeight B V S n :=
        Finset.sum_le_sum fun a ha ↦ hterm a ha
      _ = (S.card : ℝ) * (c⁻¹ * packetRankWeight B V S n) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hlower := sum_generator_mass_eq_three_mul_weight B V S hV hbraid n
  by_contra hne
  have hwpos : 0 < packetRankWeight B V S n := by
    have hwnonneg := packetRankWeight_nonneg B V S n
    exact lt_of_le_of_ne hwnonneg (Ne.symm hne)
  have hratio : (S.card : ℝ) * c⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hc]
    dsimp [c]
    linarith
  rw [hlower] at hupper
  have := mul_lt_mul_of_pos_right hratio hwpos
  nlinarith

/-- Vanishing of the integer weight means that every checked packet
displacement is literally zero on the tail. -/
theorem eventually_generator_eq_base_of_scaled_vanishing
    (B : OpAlmostRepresentation E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
    (S : Finset Γ)
    (hV : ∀ n g, IsExactInvolution (V n g))
    (hbraid : ∀ n a, a ∈ S →
      V n a * V n 1 * V n a = V n 1 * V n a * V n 1)
    (hvan : ∀ a ∈ S,
      ScaledMassVanishing B (packetRankWeight B V S)
        (fun n ↦ V n a - V n 1)) :
    ∃ N, ∀ n ≥ N, ∀ a ∈ S, V n a = V n 1 := by
  classical
  obtain ⟨N, hN⟩ :=
    eventually_packetRankWeight_eq_zero_of_scaled_vanishing
      B V S hV hbraid hvan
  refine ⟨N, fun n hn a ha ↦ ?_⟩
  letI : Nonempty (B.model n) :=
    Fintype.card_pos_iff.mp (B.modelNonempty n)
  have hweight : generatorRankWeight (V n) S = 0 := by
    have hreal := hN n hn
    unfold packetRankWeight at hreal
    exact_mod_cast hreal
  have hrank : (V n a - V n 1).rank = 0 := by
    have hle := displacementRank_le_generatorRankWeight (V n) S ha
    unfold displacementRank at hle
    omega
  have hmass : matMass (V n a - V n 1) = 0 := by
    apply le_antisymm
    · calc
        matMass (V n a - V n 1) ≤
            ((V n a - V n 1).rank : ℝ) * ‖V n a - V n 1‖ ^ 2 :=
          matMass_le_rank_mul_sq_opNorm _
        _ = 0 := by rw [hrank]; norm_num
    · exact matMass_nonneg _
  have hzero : V n a - V n 1 = 0 :=
    UltraproductScaledTransport.eq_zero_of_matMass_eq_zero hmass
  exact sub_eq_zero.mp hzero

end

end FinitePacketCollapseCore
end GroupApproximation
