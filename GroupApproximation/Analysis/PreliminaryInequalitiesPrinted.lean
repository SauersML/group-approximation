import GroupApproximation.Sofic.LeavittTraceFloor
import GroupApproximation.Sofic.PrintedPreliminaryEstimates

/-!
# The three inequalities of the notation paragraph, in the printed shape

`non_mf_groups_exist.tex`, `\section{Matrix quotients}` (the preliminary matrix estimates),
fixes the notation `tr_r`, `‖·‖`, `‖x‖₂ = tr_r(x*x)^{1/2}` on `M_r(ℂ)` and then
closes the paragraph with

> We repeatedly use the inequalities
> `‖x‖₂ ≤ ‖x‖`;  `|tr_r(x)| ≤ ‖x‖`;  and `‖uxv‖₂ = ‖x‖₂` for unitaries `u, v`.

Proof-ledger row `PRE.07` asks for the three to be located separately.  The
middle one is `PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm`, stated
in exactly the printed form.  The outer two were present in the corpus only in
*squared* form (`hsNormSq_mul_left`, `hsNormSq_mul_right`) or in *distance*
form (`hsDistSq_le_sq_l2_opNorm`), and squaring is not innocent here: the
printed sentence is an inequality between norms, and the two-sided identity
`‖uxv‖₂ = ‖x‖₂` is printed as one statement about `u` and `v` together, not as
two one-sided identities.  This file states both in the printed shape, on
`hsNorm`, and then bundles all three as `prelim_notation_inequalities`, so that
a reader of the notation paragraph has one declaration to consult and three
named declarations behind it.

The empty model is not excluded anywhere below.  There every quantity divides
by zero, which in Lean is zero, and all three assertions hold for the
uninteresting reason.  In particular the two-sided unitary identity is stated
*without* the positivity hypothesis that `hsNormSq_mul_left` carries: the
manuscript prints none, and the degenerate case is discharged internally.
-/

namespace GroupApproximation
namespace PrelimNotation

open Matrix
open scoped Matrix.Norms.L2Operator

section Inequalities

variable (Y : FiniteModel)

/-- The normalized squared Hilbert--Schmidt norm is the squared distance to
zero.  `hsDistSq` is the primitive the domination lemma is stated for. -/
theorem hsDistSq_zero_eq_hsNormSq (A : Matrix Y Y ℂ) :
    hsDistSq Y A 0 = hsNormSq Y A := by
  simp [hsDistSq, hsNormSq]

/-- Squared form of the first printed inequality: the dimension-free
domination `hsDistSq_le_sq_l2_opNorm` read at the origin. -/
theorem hsNormSq_le_sq_l2_opNorm (A : Matrix Y Y ℂ) :
    hsNormSq Y A ≤ ‖A‖ ^ 2 := by
  have h := hsDistSq_le_sq_l2_opNorm Y A 0
  rw [hsDistSq_zero_eq_hsNormSq Y A, sub_zero] at h
  exact h

/-- **The first printed inequality**: `‖x‖₂ ≤ ‖x‖`, between the norms
themselves and not their squares. -/
theorem hsNorm_le_l2_opNorm (A : Matrix Y Y ℂ) :
    hsNorm Y A ≤ ‖A‖ := by
  unfold hsNorm
  have h := Real.sqrt_le_sqrt (hsNormSq_le_sq_l2_opNorm Y A)
  rwa [Real.sqrt_sq (norm_nonneg A)] at h

/-! The second printed inequality, `|tr_r(x)| ≤ ‖x‖`, is
`PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm`: each diagonal entry
is bounded by the operator norm, the unnormalized trace is a sum of `r` of
them, and the normalization divides by `r`.  It is cited, not restated. -/

/-- Left multiplication by a unitary preserves the normalized
Hilbert--Schmidt norm.  Unlike `hsNormSq_mul_left` this carries no positivity
hypothesis on the model: an empty model makes both sides zero. -/
theorem hsNorm_mul_left {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (A : Matrix Y Y ℂ) :
    hsNorm Y (U * A) = hsNorm Y A := by
  unfold hsNorm
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with h0 | hpos
  · haveI : IsEmpty Y := Fintype.card_eq_zero_iff.mp h0
    simp [hsNormSq]
  · rw [hsNormSq_mul_left Y hU hpos A]

/-- Right multiplication by a unitary preserves the normalized
Hilbert--Schmidt norm. -/
theorem hsNorm_mul_right {V : Matrix Y Y ℂ}
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) (A : Matrix Y Y ℂ) :
    hsNorm Y (A * V) = hsNorm Y A := by
  unfold hsNorm
  rw [hsNormSq_mul_right Y hV A]

/-- **The third printed inequality**: `‖uxv‖₂ = ‖x‖₂` for unitaries `u, v`,
as the single two-sided statement the manuscript prints. -/
theorem hsNorm_unitary_mul_mul {U V : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hV : V ∈ Matrix.unitaryGroup Y ℂ)
    (A : Matrix Y Y ℂ) :
    hsNorm Y (U * A * V) = hsNorm Y A := by
  rw [hsNorm_mul_right Y hV (U * A), hsNorm_mul_left Y hU A]

end Inequalities

/-! ## The façade

The manuscript uses the three inequalities "without comment", so no single
printed statement carries them.  This structure is that statement.  Each field
is discharged by one of the named theorems above, separately: the façade
composes nothing and proves nothing on its own. -/

/-- The three inequalities the notation paragraph of the preliminary matrix estimates declares it
will use without comment, in the printed order. -/
structure PrelimNotationInequalities (Y : FiniteModel) : Prop where
  /-- `‖x‖₂ ≤ ‖x‖`. -/
  hsNorm_le_opNorm : ∀ A : Matrix Y Y ℂ, hsNorm Y A ≤ ‖A‖
  /-- `|tr_r(x)| ≤ ‖x‖`. -/
  norm_normTrace_le_opNorm : ∀ A : Matrix Y Y ℂ, ‖normTrace Y A‖ ≤ ‖A‖
  /-- `‖uxv‖₂ = ‖x‖₂` for unitaries `u, v`. -/
  hsNorm_unitary_invariant : ∀ U V : Matrix Y Y ℂ,
      U ∈ Matrix.unitaryGroup Y ℂ → V ∈ Matrix.unitaryGroup Y ℂ →
      ∀ A : Matrix Y Y ℂ, hsNorm Y (U * A * V) = hsNorm Y A

/-- **`PRE.07`.**  The three unnamed inequalities of the preliminaries hold on
every finite matrix model, each by its own named theorem. -/
theorem prelim_notation_inequalities (Y : FiniteModel) :
    PrelimNotationInequalities Y where
  hsNorm_le_opNorm := hsNorm_le_l2_opNorm Y
  norm_normTrace_le_opNorm :=
    PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm Y
  hsNorm_unitary_invariant _ _ hU hV := hsNorm_unitary_mul_mul Y hU hV

end PrelimNotation
end GroupApproximation
