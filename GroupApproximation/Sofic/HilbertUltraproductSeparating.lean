import GroupApproximation.Sofic.HilbertUltraproductFaithful
import GroupApproximation.Sofic.NormTraceGap

/-!
# The action separates: a family acting as zero is null along `ω`

`Sofic/HilbertUltraproductFaithful.lean` proves the easy direction, that an
`ω`-null family annihilates `K_ω`.  This file proves the direction the printed
proof of `thm:kazhdan-transport` actually uses:

> if `A = [A_n]_ω ≠ 0` then `lim_ω ‖A_n‖ = δ > 0`, and unit vectors `ξ_n` with
> `‖A_nξ_n‖ ≥ ‖A_n‖ - 1/n` give `‖A[ξ_n]_ω‖ = δ`

Together the two say that the kernel of the action is *exactly* the `ω`-null
families, so the action factors through `∏_ω B(K_n)` and is faithful there,
which is the manuscript's KT.04.

## The one place the weight matters

A unit vector of the *coordinate* space is the wrong test family: at the
dimension weight its class in `K_ω` is zero, because a family of fixed mass is
null against a weight tending to infinity.  The test family has to be rescaled
to carry the weight, `ξ_n = √(w n) · x_n`, and then both sides scale together:
the mass of `ξ_n` is `w n`, so its class is a unit vector of `K_ω`, and the
mass of `A_nξ_n` is `w n ‖A_n x_n‖²`, so the class of `A ξ` has norm `δ`.
That is the same normalization the manuscript performs implicitly when it says
`‖A[ξ_n]_ω‖ = δ`.

The near-attainment of the operator norm is the contrapositive of
`NormTraceGap.l2_opNorm_le_of_sum_normSq`, which the development already has.
-/

namespace GroupApproximation
namespace HilbertUltraproductSeparating

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction UltraproductScaledTransport
open HilbertUltraproductPairing ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **Near-attainment of the `l²` operator norm**, as the contrapositive of the
bound the development already proves: a matrix whose norm exceeds `M` moves
some vector by more than `M`. -/
theorem exists_sum_normSq_gt (Z : FiniteModel) (C : Matrix Z Z ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hlt : M < ‖C‖) :
    ∃ x : Z → ℂ, M ^ 2 * ∑ i : Z, Complex.normSq (x i)
      < ∑ i : Z, Complex.normSq ((C *ᵥ x) i) := by
  by_contra hcon
  have hbound : ∀ x : Z → ℂ, ∑ i : Z, Complex.normSq ((C *ᵥ x) i)
      ≤ M ^ 2 * ∑ i : Z, Complex.normSq (x i) := by
    intro x
    by_contra hx
    exact hcon ⟨x, lt_of_not_ge hx⟩
  exact absurd (l2_opNorm_le_of_sum_normSq Z C hM hbound) (not_le.mpr hlt)

/-! ## Two pieces of scalar bookkeeping

Both are about rescaling a coordinate vector by a positive real; they are what
turns "some vector is moved" into "some vector *of the weight's mass* is
moved". -/

private theorem sum_normSq_smul {ι : Type*} [Fintype ι] (t : ℝ) (v : ι → ℂ) :
    ∑ p : ι, Complex.normSq (((t : ℂ) • v) p)
      = t ^ 2 * ∑ p : ι, Complex.normSq (v p) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  show Complex.normSq ((t : ℂ) * v p) = t ^ 2 * Complex.normSq (v p)
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  ring

private theorem mulVec_const_smul {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (c : ℂ) (v : ι → ℂ) :
    A *ᵥ (c • v) = c • (A *ᵥ v) := by
  funext i
  show ∑ j, A i j * (c * v j) = c * ∑ j, A i j * v j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-! ## Near-attainment at a single stage -/

/-- **The manuscript's choice of test vectors, at the weight.**  If an operator
on `K_n` has norm above `δ`, then some coordinate matrix whose Frobenius mass
is exactly `c` is moved to mass more than `δ² c`.

The manuscript picks unit vectors `ξ_n` with `‖A_nξ_n‖ ≥ ‖A_n‖ - 1/n`.  At the
weight a *coordinate* unit vector is the wrong test family — a family of fixed
mass is null against a weight tending to infinity, so its class in `K_ω` is
zero — and the free parameter `c` here is where the weight enters: taking
`c = w n` makes the class a unit vector of `K_ω`. -/
theorem exists_matMass_moved (Z : FiniteModel)
    (A : Matrix (doubleModel Z) (doubleModel Z) ℂ) {δ c : ℝ}
    (hδ : 0 ≤ δ) (hc : 0 < c) (hA : δ < ‖A‖) :
    ∃ x : Matrix Z Z ℂ, matMass x = c ∧
      δ ^ 2 * c < matMass (rowMat (A *ᵥ rowVec x)) := by
  obtain ⟨v, hv⟩ := exists_sum_normSq_gt (doubleModel Z) A hδ hA
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∑ i, Complex.normSq (v i) = S := ⟨_, rfl⟩
  rw [hS] at hv
  have hSnn : 0 ≤ S := by
    rw [← hS]
    exact Finset.sum_nonneg fun p _ ↦ Complex.normSq_nonneg (v p)
  have hpos : 0 < ∑ i, Complex.normSq ((A *ᵥ v) i) :=
    lt_of_le_of_lt (mul_nonneg (pow_nonneg hδ 2) hSnn) hv
  have hSpos : 0 < S := by
    rcases hSnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun p _ ↦ Complex.normSq_nonneg (v p))).1 (hS.trans h.symm)
      have hv0 : v = 0 :=
        funext fun p ↦ Complex.normSq_eq_zero.1 (hall p (Finset.mem_univ p))
      rw [hv0, Matrix.mulVec_zero] at hpos
      simp at hpos
  have hSne : S ≠ 0 := ne_of_gt hSpos
  have hquot : 0 < c / S := div_pos hc hSpos
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt (c / S) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; exact Real.sqrt_pos.2 hquot
  have ht2 : t ^ 2 = c / S := by rw [ht]; exact Real.sq_sqrt hquot.le
  have hcs : t ^ 2 * S = c := by rw [ht2]; field_simp
  refine ⟨rowMat ((t : ℂ) • v), ?_, ?_⟩
  · rw [matMass_rowMat Z ((t : ℂ) • v), sum_normSq_smul, hS]
    exact hcs
  · rw [rowVec_rowMat, mulVec_const_smul, matMass_rowMat Z, sum_normSq_smul]
    calc δ ^ 2 * c = t ^ 2 * (δ ^ 2 * S) := by rw [← hcs]; ring
      _ < t ^ 2 * ∑ i, Complex.normSq ((A *ᵥ v) i) :=
          mul_lt_mul_of_pos_left hv (pow_pos htpos 2)

/-! ## The separating direction -/

variable {Y : ℕ → FiniteModel} {w : ℕ → ℝ} {ω : Ultrafilter ℕ}

/-- **A family that is not `ω`-null acts nontrivially.**  This is the half of
KT.04 the printed proof consumes: `lim_ω ‖A_n‖ = δ > 0` gives a test class of
`K_ω` that `A` does not annihilate.

The hypothesis is `0 < w n`, not `0 ≤ w n`: at a stage of zero weight every
coordinate matrix has null class, so nothing there can witness anything, and
the manuscript's weight is a dimension. -/
theorem actQ_ne_zero_of_not_tendsto (hw : ∀ n, 0 < w n)
    (a : BoundedMatrixSequence (DblIdx Y))
    (ha : ¬ Tendsto (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)
      (ω : Filter ℕ) (𝓝 0)) :
    actQ Y w ω a ≠ 0 := by
  rw [Metric.tendsto_nhds] at ha
  obtain ⟨ε, hε, hbad⟩ : ∃ ε : ℝ, 0 < ε ∧
      ¬ (∀ᶠ n in (ω : Filter ℕ),
        dist ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ 0 < ε) := by
    by_contra hcon
    refine ha fun ε hε ↦ ?_
    by_contra hbad
    exact hcon ⟨ε, hε, hbad⟩
  have hδ : 0 < ε / 2 := by linarith
  -- a positive floor for the norms, on a set of `ω`
  have hfloor : ∀ᶠ n in (ω : Filter ℕ),
      ε / 2 < ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ := by
    filter_upwards [Ultrafilter.eventually_not.2 hbad] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), not_lt] at hn
    linarith
  -- the test family: mass `w n` where the floor holds, zero elsewhere
  have hstep : ∀ n : ℕ, ∃ x : Matrix (Y n) (Y n) ℂ, matMass x ≤ w n ∧
      (ε / 2 < ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ →
        (ε / 2) ^ 2 * w n
          < matMass (rowMat ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n
              *ᵥ rowVec x))) := by
    intro n
    by_cases hn : ε / 2 < ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖
    · obtain ⟨x, hx1, hx2⟩ := exists_matMass_moved (Y n)
        ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n) hδ.le (hw n) hn
      exact ⟨x, hx1.le, fun _ ↦ hx2⟩
    · exact ⟨0, by rw [matMass_zero]; exact (hw n).le, fun h ↦ absurd h hn⟩
  choose ξ hξ1 hξ2 using hstep
  have hmem : (ξ : MatFam Y) ∈ massBounded Y w :=
    ⟨1, fun n ↦ by rw [one_mul]; exact hξ1 n⟩
  intro hzero
  have hcls : actQ Y w ω a (Submodule.Quotient.mk ⟨ξ, hmem⟩) = 0 := by
    rw [hzero, LinearMap.zero_apply]
  rw [actQ_mk, Submodule.Quotient.mk_eq_zero] at hcls
  have hnull : WeightNull Y (clipWeight w) (ω : Filter ℕ) (applyFam Y a ξ) :=
    hcls
  obtain ⟨n, hn1, hn2⟩ :=
    ((hnull ((ε / 2) ^ 2) (pow_pos hδ 2)).and hfloor).exists
  rw [clipWeight_eq w (fun m ↦ (hw m).le) n] at hn1
  have hbig := hξ2 n hn2
  have heq : applyFam Y a ξ n
      = rowMat ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n
          *ᵥ rowVec (ξ n)) := rfl
  rw [heq] at hn1
  linarith

/-- **KT.04.**  The kernel of the action on `K_ω` is exactly the families that
are null along `ω`, so the action factors through `∏_ω B(K_n)` and is faithful
*there*.  The cofinite corona the development uses to carry the action is not
faithful on `K_ω`, and this is the precise statement that survives. -/
theorem actQ_eq_zero_iff_tendsto (hw : ∀ n, 0 < w n)
    (a : BoundedMatrixSequence (DblIdx Y)) :
    actQ Y w ω a = 0 ↔
      Tendsto (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)
        (ω : Filter ℕ) (𝓝 0) := by
  refine ⟨fun h ↦ by_contra fun hcon ↦ actQ_ne_zero_of_not_tendsto hw a hcon h,
    fun h ↦ HilbertUltraproductFaithful.act_eq_zero_of_omegaNull
      (fun n ↦ (hw n).le) a h⟩

/-- **The projection-order input, in the form the printed proof uses it.**  Two
operator sequences that act identically on `K_ω` agree in `∏_ω B(K_n)`.  With
`a = QP` and `b = P` this is the step "`QP` and `P` act identically on `K_ω`,
so `QP = P`, that is, `P ≤ Q`". -/
theorem tendsto_norm_sub_of_actQ_eq (hw : ∀ n, 0 < w n)
    (a b : BoundedMatrixSequence (DblIdx Y))
    (h : actQ Y w ω a = actQ Y w ω b) :
    Tendsto (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n
        - (b : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)
      (ω : Filter ℕ) (𝓝 0) := by
  have hz : actQ Y w ω (a - b) = 0 := by
    rw [actQ_sub, h, sub_self]
  exact (actQ_eq_zero_iff_tendsto hw (a - b)).1 hz

end

end HilbertUltraproductSeparating
end GroupApproximation
