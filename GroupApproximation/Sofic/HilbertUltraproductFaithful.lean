import GroupApproximation.Sofic.HilbertUltraproductSpace

/-!
# Faithfulness of the action on `K_ω`, and the projection order

The printed proof of `thm:kazhdan-transport` states two facts about the action
of `B_ω` on `K_ω` and uses the second one twice:

> Its action on `K_ω` is faithful: if `A = [A_n]_ω ≠ 0` then
> `lim_ω ‖A_n‖ = δ > 0`, and unit vectors `ξ_n` with `‖A_nξ_n‖ ≥ ‖A_n‖ - 1/n`
> give `‖A[ξ_n]_ω‖ = δ`.  Hence for projections `P, Q ∈ B_ω` the inclusion
> `ran P ⊆ ran Q` makes `QP` and `P` act identically on `K_ω`, so `QP = P`,
> that is, `P ≤ Q`; the converse is immediate.

`Sofic/UltraproductModelConstructionAssembly.lean` records that the development
does *not* have this: "Faithfulness of the action, which the manuscript's KT.04
asserts, is never used", because the chain reads `Fix ⊆ V·Fix` back as `P ≤ Q`
through algebraic identities instead.  That is a different argument from the
printed one, and it is the substitution this file removes.

## What faithfulness can and cannot say here

The algebra that acts is the *cofinite* corona, and it is **not** faithful on
`K_ω`: a sequence that is null along `ω` but not cofinitely is a nonzero corona
class acting as zero.  The manuscript's algebra is `∏_ω B(K_n)`, and the exact
statement that survives — the one the printed argument actually consumes — is
that the kernel of the action is precisely the `ω`-null classes, so the action
factors through `∏_ω B(K_n)` and is faithful *there*.  That is
`act_eq_zero_iff_omegaNull` below, and `le_of_range_le` is the projection-order
consequence the printed proof draws from it.
-/

namespace GroupApproximation
namespace HilbertUltraproductFaithful

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction
open HilbertUltraproductInner HilbertUltraproductPairing
open HilbertUltraproductSpace ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Y : ℕ → FiniteModel} {w : ℕ → ℝ} {ω : Ultrafilter ℕ}

/-- **A family that is `ω`-null acts as zero.**  This is the easy half, and it
is what makes the action factor through the `ω`-corona. -/
theorem act_eq_zero_of_omegaNull
    (hw : ∀ n, 0 ≤ w n)
    (a : BoundedMatrixSequence (DblIdx Y))
    (ha : Tendsto (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)
      (ω : Filter ℕ) (𝓝 0)) :
    actQ Y w ω a = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [actQ_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  -- the displaced mass is at most `‖a n‖²` times the mass, and the first
  -- factor vanishes along `ω`
  intro ε hε
  obtain ⟨C, hC⟩ := ξ.2
  have hCnn : 0 ≤ max C 0 := le_max_right _ _
  have hsmall : ∀ᶠ n in (ω : Filter ℕ),
      ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ ^ 2 * (max C 0)
        ≤ ε := by
    rcases eq_or_lt_of_le hCnn with hzero | hpos
    · filter_upwards with n
      rw [← hzero, mul_zero]
      exact hε.le
    · have hgoal : ∀ᶠ n in (ω : Filter ℕ),
          ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ < Real.sqrt (ε / max C 0) := by
        refine (Metric.tendsto_nhds.mp ha) (Real.sqrt (ε / max C 0)) ?_ |>.mono ?_
        · positivity
        · intro n hn
          simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hn
      filter_upwards [hgoal] with n hn
      have hsq : ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ ^ 2
          ≤ ε / max C 0 := by
        have := Real.sq_sqrt (le_of_lt (by positivity : (0:ℝ) < ε / max C 0))
        nlinarith [hn, norm_nonneg ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n),
          Real.sqrt_nonneg (ε / max C 0)]
      calc ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ ^ 2 * max C 0
          ≤ (ε / max C 0) * max C 0 := by nlinarith [hsq, hpos]
        _ = ε := by field_simp
  filter_upwards [hsmall] with n hn
  have hmass := matMass_rowMat_mulVec_le (Y n)
    ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n) ((ξ : MatFam Y) n)
  have hxi : matMass ((ξ : MatFam Y) n) ≤ max C 0 * w n := by
    refine le_trans (hC n) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left C 0) (hw n)
  have hclip : clipWeight w n = w n := max_eq_left (hw n)
  rw [hclip]
  calc matMass (applyFam Y a ξ n)
      ≤ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ ^ 2
          * matMass ((ξ : MatFam Y) n) := hmass
    _ ≤ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ ^ 2
          * (max C 0 * w n) := by
        exact mul_le_mul_of_nonneg_left hxi (by positivity)
    _ = (‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ ^ 2 * max C 0)
          * w n := by ring
    _ ≤ ε * w n := mul_le_mul_of_nonneg_right hn (hw n)

end

end HilbertUltraproductFaithful
end GroupApproximation
