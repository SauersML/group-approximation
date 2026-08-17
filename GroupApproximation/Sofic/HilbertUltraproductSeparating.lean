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
open UltrafilterLimit UltraproductModelConstruction
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

end

end HilbertUltraproductSeparating
end GroupApproximation
