import Mathlib.GroupTheory.SpecificGroups.Dihedral
import GroupApproximation.Sofic.ExactCoronaNegativeCorner
import GroupApproximation.Sofic.FiniteGroupCoronaExactification
import GroupApproximation.Sofic.InvolutionMicrostateTools
import GroupApproximation.Sofic.ScalarCocycle

/-!
# The dihedral parity obstruction in a norm-matrix corona

The two Pauli reflections generate `DihedralGroup 4`; their product is the
quarter-turn and the central half-turn acts as `-1`.  This file isolates the
finite-dimensional obstruction needed by the tail-lifting audit.  If a
corona representation of this group sends the half-turn to the constant
sequence `-1`, finite-group corona exactification supplies genuine
same-dimensional coordinate representations.  Rigidity of exact involutions
then makes the half-turn exactly `-1` at every sufficiently late coordinate,
so the two reflections exactly anticommute.  The determinant obstruction
forces those coordinate dimensions to be even.
-/

namespace GroupApproximation
namespace DihedralCoronaParity

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The central half-turn in the order-eight dihedral group. -/
def halfTurn : DihedralGroup 4 :=
  DihedralGroup.r (2 : ZMod 4)

/-- The two adjacent reflections corresponding to the Pauli generators. -/
def reflectionX : DihedralGroup 4 :=
  DihedralGroup.sr (0 : ZMod 4)

def reflectionZ : DihedralGroup 4 :=
  DihedralGroup.sr (1 : ZMod 4)

theorem halfTurn_sq : halfTurn * halfTurn = 1 := by
  rw [halfTurn, DihedralGroup.r_mul_r]
  have hz : (2 : ZMod 4) + 2 = 0 := by decide
  rw [hz, DihedralGroup.r_zero]

/-- The adjacent-reflection identity which becomes Pauli anticommutation when
the half-turn is represented by `-1`. -/
theorem reflectionX_mul_reflectionZ :
    reflectionX * reflectionZ =
      halfTurn * (reflectionZ * reflectionX) := by
  rw [reflectionX, reflectionZ, halfTurn, DihedralGroup.sr_mul_sr,
    DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r]
  congr 1

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- A dihedral corona representation whose half-turn is the constant `-1`
cannot have odd-dimensional exactifications at sufficiently late
coordinates. -/
theorem eventually_not_odd_card
    (rho : DihedralGroup 4 →* NormMatrixCoronaUnitary X)
    (hneg : rho halfTurn = ExactCoronaNegativeCorner.coronaNegOne X) :
    ∀ᶠ n in cofinite, ¬ Odd (Fintype.card (X n)) := by
  obtain ⟨lift, hlift⟩ :=
    FiniteGroupCoronaExactification.exists_exact_coordinate_lift
      (F := DihedralGroup 4) (X := X) (fun n ↦ inferInstance) rho
  have hquot :
      (QuotientGroup.mk (fun n ↦ lift n halfTurn) :
        NormMatrixCoronaUnitary X) =
        (QuotientGroup.mk (ExactCoronaNegativeCorner.negOneSeq X) :
          NormMatrixCoronaUnitary X) := by
    simpa [ExactCoronaNegativeCorner.coronaNegOne] using
      (hlift halfTurn).trans hneg
  have hclose : ∀ᶠ n in cofinite,
      opLength (X n)
          ((lift n halfTurn)⁻¹ * ExactCoronaNegativeCorner.negOneU (X n)) < 2 :=
    (QuotientGroup.eq.mp hquot) 2 (by norm_num)
  filter_upwards [hclose] with n hn
  intro hodd
  let R : Matrix (X n) (X n) ℂ := lift n halfTurn
  have hRsqU : lift n halfTurn * lift n halfTurn = 1 := by
    simpa only [map_mul, map_one] using congrArg (lift n) halfTurn_sq
  have hRsq : R * R = 1 := by
    exact congrArg
      (fun u : Matrix.unitaryGroup (X n) ℂ ↦
        (u : Matrix (X n) (X n) ℂ)) hRsqU
  have hRunit : Rᴴ * R = 1 := by
    have hstar := Unitary.star_mul_self_of_mem (lift n halfTurn).property
    rw [Matrix.star_eq_conjTranspose] at hstar
    exact hstar
  have hRstar : Rᴴ = R := by
    calc
      Rᴴ = Rᴴ * 1 := by rw [mul_one]
      _ = Rᴴ * (R * R) := by rw [hRsq]
      _ = (Rᴴ * R) * R := by rw [mul_assoc]
      _ = R := by rw [hRunit, one_mul]
  have hRinv : InvolutionRankMass.IsExactInvolution R := ⟨hRstar, hRsq⟩
  have hnegInv : InvolutionRankMass.IsExactInvolution
      (-1 : Matrix (X n) (X n) ℂ) := by
    constructor <;> simp
  have hcomm : R * (-1 : Matrix (X n) (X n) ℂ) = -1 * R := by
    simp
  rw [opLength_inv_mul] at hn
  have hdist : ‖R - (-1 : Matrix (X n) (X n) ℂ)‖ < 2 := by
    rw [← norm_sub_rev]
    simpa [R, ExactCoronaNegativeCorner.coe_negOneU] using hn
  have hReq : R = (-1 : Matrix (X n) (X n) ℂ) :=
    InvolutionMicrostateTools.eq_of_norm_sub_lt_two
      hRinv hnegInv hcomm hdist
  let U : Matrix (X n) (X n) ℂ := lift n reflectionX
  let V : Matrix (X n) (X n) ℂ := lift n reflectionZ
  have huvU :
      lift n reflectionX * lift n reflectionZ =
        lift n halfTurn * (lift n reflectionZ * lift n reflectionX) := by
    simpa only [map_mul] using
      congrArg (lift n) reflectionX_mul_reflectionZ
  have hhalf :
      ((lift n halfTurn : Matrix.unitaryGroup (X n) ℂ) :
        Matrix (X n) (X n) ℂ) = -1 := by
    simpa [R] using hReq
  have huv : U * V = (-1 : ℂ) • (V * U) := by
    have := congrArg
      (fun u : Matrix.unitaryGroup (X n) ℂ ↦
        (u : Matrix (X n) (X n) ℂ)) huvU
    simpa [U, V, hhalf] using this
  have hpow := pow_card_eq_one_of_scalarCommute (X n)
    (lift n reflectionX).property (lift n reflectionZ).property huv
  rw [hodd.neg_one_pow] at hpow
  exact (by norm_num : (-1 : ℂ) ≠ 1) hpow

end

end DihedralCoronaParity
end GroupApproximation
