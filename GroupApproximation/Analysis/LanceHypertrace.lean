import GroupApproximation.Analysis.LanceMultiplicationOperator
import GroupApproximation.Analysis.GroupVonNeumannTrace
import GroupApproximation.Analysis.CStarMatrixFactorization

/-!
# The canonical trace as a functional on bounded operators

Toward proof-ledger row `RE.05` (the Lance debt).  Lance's argument evaluates
the canonical trace of `L(G)` on the image of a multiplication operator under
a completely positive approximation.  This module collects what that
evaluation needs, on the *ambient* operator algebra where the composite lives:

* `coefficientAtOne` — the identity coefficient `T ↦ (T δ₁) 1`, as a plain
  function (`ReducedGroupCStarTrace.ambientCoefficientAtOne` is the same map
  packaged as a continuous linear map);
* `coefficientAtOne_eq_inner` — it is the vector state at `δ₁`, hence
* `coefficientAtOne_nonneg` — nonnegative on positive operators, and
* `norm_coefficientAtOne_le` — contractive, since `δ₁` is a unit vector;
* `coefficientAtOne_conj_leftRegular` — invariant under conjugation by a
  left translation, for operators in `L(G)` (traciality of the coefficient,
  through `GroupVonNeumann.coefficient_mul_comm`).

The last one is the reason the whole argument produces an *invariant* mean
rather than merely a state: conjugation by `λ_g` moves the symbol of a
multiplication operator (`leftRegular_conj_mulOp`) and leaves the trace
alone.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open ReducedGroupCStarTrace GroupVonNeumann

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The identity coefficient of a bounded operator: the canonical trace of
`L(G)`, before restriction. -/
def coefficientAtOne (T : GroupHilbert G →L[ℂ] GroupHilbert G) : ℂ :=
  (T (deltaOne G)) 1

/-- The coefficient is the vector state at the unit vector `δ₁`. -/
theorem coefficientAtOne_eq_inner (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    coefficientAtOne T = ⟪deltaOne G, T (deltaOne G)⟫_ℂ := by
  classical
  rw [coefficientAtOne, deltaOne, lp.inner_single_left]
  simp

theorem coefficientAtOne_one :
    coefficientAtOne (1 : GroupHilbert G →L[ℂ] GroupHilbert G) = 1 :=
  coefficient_one G

@[simp]
theorem coefficientAtOne_add (T S : GroupHilbert G →L[ℂ] GroupHilbert G) :
    coefficientAtOne (T + S) = coefficientAtOne T + coefficientAtOne S := rfl

@[simp]
theorem coefficientAtOne_smul (c : ℂ)
    (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    coefficientAtOne (c • T) = c * coefficientAtOne T := rfl

/-- The coefficient is nonnegative on positive operators, and real. -/
theorem coefficientAtOne_nonneg {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : 0 ≤ T) : ∃ r : ℝ, 0 ≤ r ∧ coefficientAtOne T = r := by
  obtain ⟨S, hS⟩ := exists_star_mul_self_of_nonneg hT
  refine ⟨‖S (deltaOne G)‖ ^ 2, by positivity, ?_⟩
  rw [coefficientAtOne, hS]
  have h := coefficient_star_mul_self G S
  rw [h]
  push_cast
  ring

/-- The coefficient is contractive: `δ₁` is a unit vector. -/
theorem norm_coefficientAtOne_le (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    ‖coefficientAtOne T‖ ≤ ‖T‖ := by
  rw [coefficientAtOne_eq_inner]
  calc ‖⟪deltaOne G, T (deltaOne G)⟫_ℂ‖
      ≤ ‖deltaOne G‖ * ‖T (deltaOne G)‖ := norm_inner_le_norm _ _
    _ ≤ ‖deltaOne G‖ * (‖T‖ * ‖deltaOne G‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖T‖ := by rw [norm_deltaOne]; ring

/-- **Trace invariance under conjugation by a left translation.**  For
operators in `L(G)`, the identity coefficient does not see the conjugation
that `leftRegular_conj_mulOp` performs on symbols. -/
theorem coefficientAtOne_conj_leftRegular (s : G)
    {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ groupVonNeumannAlgebra G) :
    coefficientAtOne (leftRegularOperator G s * T
        * star (leftRegularOperator G s))
      = coefficientAtOne T := by
  have hLreg : leftRegularOperator G s ∈ groupVonNeumannAlgebra G :=
    leftRegularOperator_mem G s
  have hstarL : star (leftRegularOperator G s) ∈ groupVonNeumannAlgebra G := by
    rw [star_leftRegularOperator]
    exact leftRegularOperator_mem G s⁻¹
  have hprod : leftRegularOperator G s * T ∈ groupVonNeumannAlgebra G :=
    (groupVonNeumannAlgebra G).mul_mem' hLreg hT
  have hcomm := coefficient_mul_comm G hprod hstarL
  calc coefficientAtOne (leftRegularOperator G s * T
        * star (leftRegularOperator G s))
      = ((leftRegularOperator G s * T * star (leftRegularOperator G s))
          (deltaOne G)) 1 := rfl
    _ = ((star (leftRegularOperator G s) * (leftRegularOperator G s * T))
          (deltaOne G)) 1 := hcomm
    _ = coefficientAtOne T := by
        have hunit : star (leftRegularOperator G s)
            * (leftRegularOperator G s * T) = T := by
          rw [← mul_assoc, star_leftRegularOperator]
          have hinv : leftRegularOperator G s⁻¹ * leftRegularOperator G s
              = 1 := by
            refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
            show (leftRegularOperator G s⁻¹
              (leftRegularOperator G s x)) g = x g
            show (leftRegularOperator G s x) (s⁻¹⁻¹ * g) = x g
            show x (s⁻¹ * (s⁻¹⁻¹ * g)) = x g
            rw [inv_inv, inv_mul_cancel_left]
          rw [hinv, one_mul]
        rw [hunit]
        rfl

/-- The bound-choice in `mulOp` is irrelevant: two bounds for the same
symbol give the same operator. -/
theorem mulOp_congr (f : G → ℂ) (C C' : ℝ) (hC : ∀ g, ‖f g‖ ≤ C)
    (hC' : ∀ g, ‖f g‖ ≤ C') : mulOp f C hC = mulOp f C' hC' := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  rfl

end

end CStarExactness
end GroupApproximation
