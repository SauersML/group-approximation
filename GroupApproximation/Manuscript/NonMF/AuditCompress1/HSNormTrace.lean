import GroupApproximation.Sofic.LeavittTraceFloor
import GroupApproximation.Sofic.HyperlinearScalar
import GroupApproximation.Meta.AxiomGuard

/-!
# The normalized Hilbert--Schmidt norm as a normalized trace

`non_mf_groups_exist.tex`, subsection "Kazhdan transport in normalized
Hilbert--Schmidt norm", lines 405--409:

> For $a\in M_d(\C)$ write
> \[
>  \hsnorm{a}=\tr_d(a^*a)^{1/2},
>  \qquad \tr_d=\frac1d\operatorname{Tr}.
> \]

The corpus defines `GroupApproximation.hsNorm Y a` as the square root of the
normalized entrywise sum `hsNormSq Y a = (∑ᵢⱼ |aᵢⱼ|²)/d`, and
`GroupApproximation.normTrace Y b = Tr b / d`. The endpoint shows these are
the printed notions:
* `tr_d(a*a)` is the real number `‖a‖₂²`;
* `‖a‖₂ = tr_d(a*a)^{1/2}`;
* `tr_d = (1/d) Tr`.

Proof route.
* `ofReal_hsNormSq` gives `hsNormSq Y A = tr_d(A A*)`. Applied to `A = a*`,
  with `hsNormSq_conjTranspose`, it gives `hsNormSq Y a = tr_d(a* a)`.
* `‖a‖₂² = hsNormSq Y a` by `Real.sq_sqrt`.
* The last clause is the definition of `normTrace` rewritten.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditCompress1

open Matrix

/-- tex 405--409: for `a ∈ M_d(ℂ)`, `tr_d(a*a)` is the real number `‖a‖₂²`,
`‖a‖₂ = tr_d(a*a)^{1/2}`, and `tr_d = (1/d) Tr`. -/
theorem manuscriptSentence_hsNormTraceFormula (Y : FiniteModel)
    (a : Matrix Y Y ℂ) :
    normTrace Y (aᴴ * a) = ((hsNorm Y a ^ 2 : ℝ) : ℂ) ∧
      hsNorm Y a = Real.sqrt ((normTrace Y (aᴴ * a)).re) ∧
      ∀ b : Matrix Y Y ℂ,
        normTrace Y b = (1 / (Fintype.card Y : ℂ)) * Matrix.trace b := by
  have h := ofReal_hsNormSq Y aᴴ
  rw [Matrix.conjTranspose_conjTranspose, hsNormSq_conjTranspose] at h
  have hsq : hsNorm Y a ^ 2 = hsNormSq Y a :=
    Real.sq_sqrt (hsNormSq_nonneg Y a)
  refine ⟨?_, ?_, fun b ↦ ?_⟩
  · rw [hsq, h]
  · show Real.sqrt (hsNormSq Y a) = _
    rw [← h, Complex.ofReal_re]
  · show Matrix.trace b / (Fintype.card Y : ℂ) = _
    rw [one_div, div_eq_inv_mul]

#audit_axioms manuscriptSentence_hsNormTraceFormula

end GroupApproximation.Manuscript.NonMF.AuditCompress1
