import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerBlocks
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-26, part 5: commutator algebra for the Powers--Størmer assembly

Finite-dimensional identities and estimates over an arbitrary finite index type `n`:

* the commutator of `Yd + iD` with `X` splits as `[Yd, X] + i[D, X]`, which gives
  `‖[Yd, X]‖₂² ≤ ‖[Yd + iD, X]‖₂²` for Hermitian `Yd`, `D` and `X`;
* `re tr([Yd + iD, X] G) ≤ |tr([Yd, X] G)| + |tr(D X G)| + |tr(X D G)|`;
* two Cauchy--Schwarz estimates `|tr(D T² G)|² ≤ tr(T²) tr(D² T²)` for unitary `G`;
* block identities for the Hermitian doubling `[[0, y], [yᴴ, 0]]`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutator with `Yd + iD` splits. -/
theorem powersStormer_commutator_add_I_smul (Yd D X : Matrix n n ℂ) :
    (Yd + Complex.I • D) * X - X * (Yd + Complex.I • D)
      = (Yd * X - X * Yd) + Complex.I • (D * X - X * D) := by
  rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_commutator_add_I_smul

/-- The commutator of two Hermitian matrices is skew-adjoint. -/
theorem powersStormer_commutator_conjTranspose {A B : Matrix n n ℂ} (hA : Aᴴ = A)
    (hB : Bᴴ = B) : (A * B - B * A)ᴴ = -(A * B - B * A) := by
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hA, hB, neg_sub]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_commutator_conjTranspose

/-- For Hermitian `Yd`, `D` and `X`: `‖[Yd, X]‖₂² ≤ ‖[Yd + iD, X]‖₂²`. -/
theorem powersStormer_re_trace_gram_commutator_le {Yd D X : Matrix n n ℂ} (hY : Ydᴴ = Yd)
    (hD : Dᴴ = D) (hX : Xᴴ = X) :
    (trace ((Yd * X - X * Yd)ᴴ * (Yd * X - X * Yd))).re
      ≤ (trace (((Yd + Complex.I • D) * X - X * (Yd + Complex.I • D))ᴴ
          * ((Yd + Complex.I • D) * X - X * (Yd + Complex.I • D)))).re := by
  rw [powersStormer_commutator_add_I_smul Yd D X,
    powersStormer_trace_gram_add_I_smul (powersStormer_commutator_conjTranspose hY hX)
      (powersStormer_commutator_conjTranspose hD hX), Complex.add_re]
  linarith [powersStormer_re_trace_gram_nonneg (D * X - X * D)]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_re_trace_gram_commutator_le

/-- `re tr([Yd + iD, X] G) ≤ |tr([Yd, X] G)| + (|tr(D X G)| + |tr(X D G)|)`. -/
theorem powersStormer_re_trace_commutator_mul_le (Yd D X G : Matrix n n ℂ) :
    (trace (((Yd + Complex.I • D) * X - X * (Yd + Complex.I • D)) * G)).re
      ≤ ‖trace ((Yd * X - X * Yd) * G)‖ + (‖trace (D * X * G)‖ + ‖trace (X * D * G)‖) := by
  have e : trace (((Yd + Complex.I • D) * X - X * (Yd + Complex.I • D)) * G)
      = trace ((Yd * X - X * Yd) * G)
        + Complex.I * (trace (D * X * G) - trace (X * D * G)) := by
    rw [powersStormer_commutator_add_I_smul Yd D X, add_mul, trace_add, smul_mul_assoc,
      trace_smul, smul_eq_mul, sub_mul (D * X) (X * D) G, trace_sub]
  rw [e]
  refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_)
  rw [norm_mul, Complex.norm_I, one_mul]
  linarith [norm_sub_le (trace (D * X * G)) (trace (X * D * G))]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_re_trace_commutator_mul_le

/-- `tr(Zᴴ X) = conj tr(Z Xᴴ)`. -/
theorem powersStormer_trace_conjTranspose_mul (Z X : Matrix n n ℂ) :
    trace (Zᴴ * X) = star (trace (Z * Xᴴ)) := by
  rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, trace_mul_comm]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_trace_conjTranspose_mul
