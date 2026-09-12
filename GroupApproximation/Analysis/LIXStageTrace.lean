import GroupApproximation.Analysis.LIXStageAlgebra
import GroupApproximation.Analysis.ShulmanTraceClasses

/-!
# A tracial state on every stage algebra of the LIX tower

`A_i = E_i · M_{E_i}(C(X_i)) · E_i` carries, at every point `w ∈ X_i`, the normalized fibre
trace

    a ↦ r_i⁻¹ · tr (a(w)),        r_i = rank E_i = stageRank n i.

It is a tracial state: it is linear, it sends the unit `E_i` to `1` because `tr E_i(w) = r_i`, it
is nonnegative on `a⋆ a` because `tr (Mᴴ M) = ∑ |M_{kj}|²`, and it is tracial because
`tr (M N) = tr (N M)`.

These traces are not compatible with the connecting maps of the tower, and nothing here asks them
to be: `Analysis/LIXLimitTrace` only needs every level to carry *some* tracial state, and
extracts a compatible family by compactness.
-/

namespace GroupApproximation
namespace STW59
namespace Gen

open scoped Matrix ComplexOrder

noncomputable section

/-- `tr (Mᴴ M)` is a nonnegative complex number: it is `∑ j k, star (M k j) * M k j`. -/
theorem stageTrace_conjTranspose_mul_self_nonneg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) :
    0 ≤ (Mᴴ * M).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => star_mul_self_nonneg (M k j)

/-- The normalized fibre trace of `A_i` at the point `w`, as a complex-linear functional. -/
def stageTraceLinearMap (n i : ℕ) (w : baseX n i) : StageAlgebra n i →ₗ[ℂ] ℂ where
  toFun a := ((stageRank n i : ℕ) : ℂ)⁻¹ * (stageEval n i w a).trace
  map_add' a b := by
    simp only [stageEval_add, Matrix.trace_add, mul_add]
  map_smul' c a := by
    have hs : stageEval n i w (c • a) = c • stageEval n i w a := rfl
    simp only [hs, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul]
    ring

theorem stageTraceLinearMap_apply (n i : ℕ) (w : baseX n i) (a : StageAlgebra n i) :
    stageTraceLinearMap n i w a = ((stageRank n i : ℕ) : ℂ)⁻¹ * (stageEval n i w a).trace :=
  rfl

/-- **The normalized fibre trace at `w` is a tracial state on `A_i`.**  The rank `r_i = 2^i · n`
is nonzero exactly when `n` is, which is where `[NeZero n]` enters. -/
def stageTracialState (n i : ℕ) [NeZero n] (w : baseX n i) :
    TracialState (StageAlgebra n i) where
  toLinearMap := stageTraceLinearMap n i w
  map_one := by
    rw [stageTraceLinearMap_apply, trace_stageEval_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (stageRank_pos n i).ne')
  map_star_mul_self_nonneg a := by
    rw [stageTraceLinearMap_apply, stageEval_mul, stageEval_star]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (stageTrace_conjTranspose_mul_self_nonneg _)
  map_mul_comm a b := by
    rw [stageTraceLinearMap_apply, stageTraceLinearMap_apply, stageEval_mul, stageEval_mul,
      Matrix.trace_mul_comm]

/-- Every stage algebra of the rank-`n` tower carries a tracial state. -/
theorem nonempty_tracialState_stageAlgebra (n i : ℕ) [NeZero n] :
    Nonempty (TracialState (StageAlgebra n i)) :=
  ⟨stageTracialState n i (stagePoint n i)⟩

end

end Gen
end STW59
end GroupApproximation
