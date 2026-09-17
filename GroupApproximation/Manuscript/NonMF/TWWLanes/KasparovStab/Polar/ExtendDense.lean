import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendBoundedStatement
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Approx
import GroupApproximation.Meta.AxiomGuard

/-!
# Polar unitary, lane `nm-tww-17b`: the absolute value has dense range

Step 2 of Lance, Thm. 3.5. Suppose `T : E → F` is adjointable, `T` and `T⋆` have dense range,
`T⋆` is bounded by `C`, and `T⋆T x` lies in the closure of the range of `S` for every `x`.
Then `S` has dense range.

Route. Given `y` and `ε`, pick `w` with `‖T⋆w - y‖ ≤ ε/2`, then `x` with
`‖Tx - w‖ ≤ ε/(2(C+1))`. Then `‖T⋆Tx - y‖ ≤ C ‖Tx - w‖ + ε/2 ≤ ε`, and `T⋆Tx` lies in the
closure of the range of `S`. The closure is closed (`IsApprox.of_approx`).
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

open GroupApproximation.HilbertModule

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **The range of `S` is dense** when it approximates `T⋆T` and `T⋆` is bounded. -/
theorem hasDenseRange_of_approx_adjoint_comp {E F : CStarModule.{v, v} B}
    (T : Adjointable E F) (S : Adjointable E E)
    (hS : ∀ x : E.carrier, IsApprox S (T.adj (T.toFun x)))
    (hT : HasDenseRange T) (hT' : HasDenseRange (Adjointable.adjoint T))
    (hb : (Adjointable.adjoint T).IsBounded) : HasDenseRange S := by
  obtain ⟨C, hC0, hC⟩ := hb
  intro y
  refine IsApprox.of_approx S fun ε hε => ?_
  have hK : 0 < C + 1 := by linarith
  obtain ⟨w, hw⟩ := hT' y (ε / 2) (half_pos hε)
  obtain ⟨x, hx⟩ := hT w (ε / 2 / (C + 1)) (div_pos (half_pos hε) hK)
  refine ⟨T.adj (T.toFun x), hS x, ?_⟩
  have hw' : E.norm (T.adj w - y) ≤ ε / 2 := hw
  have h1 : E.norm (T.adj (T.toFun x) - T.adj w) ≤ ε / 2 := by
    have hsub : T.adj (T.toFun x) - T.adj w = T.adj (T.toFun x - w) :=
      ((Adjointable.adjoint T).map_sub (T.toFun x) w).symm
    rw [hsub]
    calc E.norm (T.adj (T.toFun x - w)) ≤ C * F.norm (T.toFun x - w) := hC (T.toFun x - w)
      _ ≤ (C + 1) * (ε / 2 / (C + 1)) :=
        mul_le_mul (by linarith) hx (F.norm_nonneg _) hK.le
      _ = ε / 2 := mul_div_cancel₀ _ hK.ne'
  calc E.norm (T.adj (T.toFun x) - y)
      ≤ E.norm (T.adj (T.toFun x) - T.adj w) + E.norm (T.adj w - y) := modNorm_sub_le E _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 hw'
    _ = ε := add_halves ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.hasDenseRange_of_approx_adjoint_comp

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab
