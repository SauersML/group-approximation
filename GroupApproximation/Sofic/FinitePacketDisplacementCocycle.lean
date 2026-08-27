import GroupApproximation.Sofic.FinitePacketRankWeight
import GroupApproximation.Sofic.FinitePacketDelormeDiagonalization
import GroupApproximation.Kazhdan.UltralimitGaussianBoundedness

/-!
# The normalized displacement cocycle of an exact finite packet

An exactly covariant packet orbit has an exact displacement cocycle after
normalization by any common nonnegative weight.  A rank-weight mass estimate
gives a uniform bound for each orbit value.  These facts supply the abstract
cocycle inputs of `FinitePacketDelormeCenter` without any commutativity
hypothesis on the packet.
-/

namespace GroupApproximation
namespace FinitePacketDisplacementCocycle

open Matrix Ultralimit KazhdanCornerMatrices
open InvolutionCollapseCocycle InvolutionCollapseCenter
open InvolutionMicrostateTools
open UltralimitGaussian
open FinitePacketRankWeight ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

noncomputable section

universe u

variable {Γ : Type u} [Group Γ]
variable {Y : ℕ → Type*} [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)]

/-- The flattened packet displacement, normalized by the square root of its
stage weight and defined to be zero at zero weight. -/
def normalizedDisplacement (w : ℕ → ℝ)
    (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (g : Γ) (n : ℕ) : EuclideanSpace ℂ (Y n × Y n) :=
  if 0 < w n then
    (Real.sqrt (w n))⁻¹ • flatE (V n g - V n 1)
  else 0

omit [(n : ℕ) → DecidableEq (Y n)] in
/-- At positive weight, the normalized squared norm is mass divided by the
weight. -/
theorem norm_normalizedDisplacement_sq_of_pos
    (w : ℕ → ℝ) (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    {g : Γ} {n : ℕ} (hw : 0 < w n) :
    ‖normalizedDisplacement w V g n‖ ^ 2 =
      matMass (V n g - V n 1) / w n := by
  rw [normalizedDisplacement, if_pos hw, norm_smul, mul_pow, norm_flatE_sq]
  have hsqrt : (0 : ℝ) < Real.sqrt (w n) := Real.sqrt_pos.mpr hw
  have hnorm : ‖(Real.sqrt (w n))⁻¹‖ ^ 2 = (w n)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), inv_pow,
      Real.sq_sqrt hw.le]
  rw [hnorm]
  ring

omit [(n : ℕ) → DecidableEq (Y n)] in
/-- A mass bound linear in the weight gives a pointwise norm bound for the
normalized packet displacement. -/
theorem norm_normalizedDisplacement_le
    (w : ℕ → ℝ)
    (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (C : Γ → ℝ) (hC : ∀ g, 0 ≤ C g)
    (hmass : ∀ n g, matMass (V n g - V n 1) ≤ C g * w n)
    (g : Γ) (n : ℕ) :
    ‖normalizedDisplacement w V g n‖ ≤ Real.sqrt (C g) := by
  by_cases hpos : 0 < w n
  · have hsq := norm_normalizedDisplacement_sq_of_pos w V
      (g := g) (n := n) hpos
    have hsqle : ‖normalizedDisplacement w V g n‖ ^ 2 ≤ C g := by
      rw [hsq, div_le_iff₀ hpos]
      exact hmass n g
    have hnn := norm_nonneg (normalizedDisplacement w V g n)
    nlinarith [Real.sq_sqrt (hC g), Real.sqrt_nonneg (C g)]
  · rw [normalizedDisplacement, if_neg hpos, norm_zero]
    exact Real.sqrt_nonneg _

omit [(n : ℕ) → DecidableEq (Y n)] in
/-- Squared-norm form of the normalized displacement bound. -/
theorem norm_normalizedDisplacement_sq_le
    (w : ℕ → ℝ)
    (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (C : Γ → ℝ) (hC : ∀ g, 0 ≤ C g)
    (hmass : ∀ n g, matMass (V n g - V n 1) ≤ C g * w n)
    (g : Γ) (n : ℕ) :
    ‖normalizedDisplacement w V g n‖ ^ 2 ≤ C g := by
  have hnorm := norm_normalizedDisplacement_le w V C hC hmass g n
  nlinarith [norm_nonneg (normalizedDisplacement w V g n),
    Real.sq_sqrt (hC g), Real.sqrt_nonneg (C g)]

omit [(n : ℕ) → DecidableEq (Y n)] in
/-- The normalized displacement orbit is bounded whenever its mass is
bounded linearly at the common weight. -/
theorem isBoundedSeq_normalizedDisplacement
    (w : ℕ → ℝ)
    (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (C : Γ → ℝ) (hC : ∀ g, 0 ≤ C g)
    (hmass : ∀ n g, matMass (V n g - V n 1) ≤ C g * w n)
    (g : Γ) :
    IsBoundedSeq (normalizedDisplacement w V g) :=
  ⟨Real.sqrt (C g), norm_normalizedDisplacement_le w V C hC hmass g⟩

omit [(n : ℕ) → DecidableEq (Y n)] in
/-- The displacement at the identity is zero at every stage. -/
theorem normalizedDisplacement_one
    (w : ℕ → ℝ) (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ) (n : ℕ) :
    normalizedDisplacement w V 1 n = 0 := by
  rw [normalizedDisplacement]
  split_ifs
  · rw [sub_self, flatE_zero, smul_zero]
  · rfl

/-- Exact covariance makes the normalized packet displacement an exact
cocycle for the flattened adjoint action. -/
theorem normalizedDisplacement_cocycle
    (w : ℕ → ℝ)
    (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (U : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (hcov : ∀ n a x,
      V n (a * x) = U n a * V n x * (U n a)ᴴ)
    (n : ℕ) (a γ : Γ) :
    normalizedDisplacement w V γ n =
      adFlat (U n a) (normalizedDisplacement w V (a⁻¹ * γ) n) +
        normalizedDisplacement w V a n := by
  by_cases hpos : 0 < w n
  · let μ : Γ := a⁻¹ * γ
    have hmul : a * μ = γ := by
      dsimp [μ]
      group
    have hγ := hcov n a μ
    rw [hmul] at hγ
    have ha := hcov n a 1
    simp only [mul_one] at ha
    have hmat : V n γ - V n 1 =
        U n a * (V n μ - V n 1) * (U n a)ᴴ + (V n a - V n 1) := by
      rw [hγ, ha]
      noncomm_ring
    rw [normalizedDisplacement, if_pos hpos,
      normalizedDisplacement, if_pos hpos,
      normalizedDisplacement, if_pos hpos,
      adFlat_real_smul, adFlat_flatE, ← smul_add, ← flatE_add, hmat]
  · simp only [normalizedDisplacement, hpos, if_false]
    have hadzero : adFlat (U n a)
        (0 : EuclideanSpace ℂ (Y n × Y n)) = 0 := by
      have hunflat : unflatE
          (0 : EuclideanSpace ℂ (Y n × Y n)) = 0 := by
        ext i j
        rfl
      unfold adFlat
      rw [hunflat, Matrix.mul_zero, Matrix.zero_mul, flatE_zero]
    rw [hadzero, zero_add]

/-- The exact cocycle identity has zero limiting defect, in the form consumed
by the finite-packet Delorme theorem. -/
theorem seqNorm_cocycleDefect_eq_zero
    (w : ℕ → ℝ)
    (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (U : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (hcov : ∀ n a x,
      V n (a * x) = U n a * V n x * (U n a)ᴴ)
    (a γ : Γ) :
    seqNorm (fun n ↦
      normalizedDisplacement w V γ n -
        (adFlat (U n a) (normalizedDisplacement w V (a⁻¹ * γ) n) +
          normalizedDisplacement w V a n)) = 0 := by
  have hzero : (fun n ↦
      normalizedDisplacement w V γ n -
        (adFlat (U n a) (normalizedDisplacement w V (a⁻¹ * γ) n) +
          normalizedDisplacement w V a n)) =
      fun n ↦ (0 : EuclideanSpace ℂ (Y n × Y n)) := by
    funext n
    rw [normalizedDisplacement_cocycle w V U hcov n a γ, sub_self]
  rw [hzero]
  exact seqNorm_eq_zero_of_vanishing isBoundedSeq_zero
    (fun ε hε ↦ ⟨0, fun n _ ↦ by simpa using hε.le⟩)

/-- The exact normalized cocycle satisfies the limiting displacement identity
used by the scalar Delorme--Gaussian bound. -/
theorem profile_halmost
    (w : ℕ → ℝ)
    (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (U : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (hU : ∀ n g, U n g ∈ Matrix.unitaryGroup (Y n) ℂ)
    (hcov : ∀ n a x,
      V n (a * x) = U n a * V n x * (U n a)ᴴ)
    (g h : Γ) :
    ArchimedeanClass.stdPart
        (Hyperreal.ofSeq fun n ↦
          ‖normalizedDisplacement w V (g⁻¹ * h) n‖ ^ 2) =
      ArchimedeanClass.stdPart
        (Hyperreal.ofSeq fun n ↦
          ‖normalizedDisplacement w V h n -
            normalizedDisplacement w V g n‖ ^ 2) := by
  have hseq : (fun n ↦
      ‖normalizedDisplacement w V (g⁻¹ * h) n‖ ^ 2) =
      fun n ↦ ‖normalizedDisplacement w V h n -
        normalizedDisplacement w V g n‖ ^ 2 := by
    funext n
    have hc := normalizedDisplacement_cocycle w V U hcov n g h
    have heq : normalizedDisplacement w V h n -
        normalizedDisplacement w V g n =
      adFlat (U n g) (normalizedDisplacement w V (g⁻¹ * h) n) := by
      rw [hc]
      abel
    rw [heq, norm_adFlat (hU n g)]
  rw [hseq]

/-- Property `(T)` turns the elementwise rank-weight bound into one uniform
bound for the full normalized packet profile. -/
theorem exists_uniform_profile_bound
    (w : ℕ → ℝ)
    (V : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (U : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (hU : ∀ n g, U n g ∈ Matrix.unitaryGroup (Y n) ℂ)
    (hcov : ∀ n a x,
      V n (a * x) = U n a * V n x * (U n a)ᴴ)
    (C : Γ → ℝ) (hC : ∀ g, 0 ≤ C g)
    (hmass : ∀ n g, matMass (V n g - V n 1) ≤ C g * w n)
    {Q : Finset Γ} {κ : ℝ} (hpair : IsKazhdanPair.{u, u} Γ Q κ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g,
      seqNormSq (normalizedDisplacement w V g) ≤ R := by
  have hbdd : ∀ g : Γ, ∃ D : ℝ, ∀ n,
      ‖normalizedDisplacement w V g n‖ ^ 2 ≤ D :=
    fun g ↦ ⟨C g, norm_normalizedDisplacement_sq_le w V C hC hmass g⟩
  have hone : ∀ n, normalizedDisplacement w V 1 n = 0 :=
    normalizedDisplacement_one w V
  obtain ⟨R, hR⟩ := profile_bounded_of_isKazhdanPair hpair hbdd hone
    (profile_halmost w V U hU hcov)
  refine ⟨max R 0, le_max_right _ _, fun g ↦ ?_⟩
  exact (hR g).trans (le_max_left _ _)

end

end FinitePacketDisplacementCocycle
end GroupApproximation
