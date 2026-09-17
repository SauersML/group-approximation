import GroupApproximation.Manuscript.NonMFNotes.Full.Arithmetic.Reduction

/-!
# `thm:mf-arithmetic`: arithmetical complexity of MF recognition

Manuscript `non_mf_group_notes.tex`, `thm:mf-arithmetic`:

> "For finite presentation codes,
> `MF_fp ∈ Π⁰₂ ∖ Π⁰₁` and `NONMF_fp ∈ Σ⁰₂ ∖ Σ⁰₁`.
> Moreover the complement of the uniform word problem many-one reduces to
> `NONMF_fp`."

and its proof: "`P ∈ MF_fp ⟺ ∀ n ∃ c C_MF(P,n,c)` for a recursive `C_MF`.
Corollary `cor:undecidable` supplies properness over the first level and the
displayed reduction."

Route.
* The `Π⁰₂` upper bound is the repository's matrix-certificate checker
  `MFRecognitionSecondLevel.mfCode_pi02` (the same theorem as
  `Manuscript.MFRecognition.Recognition.mfPresentations_pi02`), and
  `Σ⁰₂` for the complement is `MFRecognitionSecondLevel.nonMFCode_sigma02`.
  `ArithmeticalHierarchy.Pi02 p` is `∃ q RE, ∀ a, p a ↔ ∀ n, q (a, n)`, which
  is the printed `∀ n ∃ c` normal form.
* Properness over the first level is derived here along the printed route:
  `NONMF_fp` is not RE because the non-RE complement of the uniform word
  problem many-one reduces to it (`Full/Arithmetic/Reduction.lean`).  Hence
  `MF_fp ∉ Π⁰₁` (its complement is not RE) and `NONMF_fp ∉ Σ⁰₁`.
-/

namespace GroupApproximation.Full.NN11

open ArithmeticalHierarchy MFRecognitionSecondLevel

/-- **`thm:mf-arithmetic`, `MF_fp ∈ Π⁰₂ ∖ Π⁰₁`** (`non_mf_group_notes.tex`). -/
theorem mfCode_pi02_not_pi01 : Pi02 MFCode ∧ ¬ Pi01 MFCode :=
  (strict_first_level_pair mfCode_pi02 nonMFCode_not_re_via_reduction).1

/-- **`thm:mf-arithmetic`, `NONMF_fp ∈ Σ⁰₂ ∖ Σ⁰₁`** (`non_mf_group_notes.tex`). -/
theorem nonMFCode_sigma02_not_sigma01 : Sigma02 NonMFCode ∧ ¬ Sigma01 NonMFCode :=
  (strict_first_level_pair mfCode_pi02 nonMFCode_not_re_via_reduction).2

/-- **`thm:mf-arithmetic`, every printed clause, in printed order**
(`non_mf_group_notes.tex`):

1. `MF_fp ∈ Π⁰₂`;
2. `MF_fp ∉ Π⁰₁`;
3. `NONMF_fp ∈ Σ⁰₂`;
4. `NONMF_fp ∉ Σ⁰₁`;
5. "the complement of the uniform word problem many-one reduces to
   `NONMF_fp`".

No hypothesis and no literature input. -/
theorem notesMFArithmetic :
    Pi02 MFCode ∧ ¬ Pi01 MFCode ∧ Sigma02 NonMFCode ∧ ¬ Sigma01 NonMFCode ∧
      (fun x => ¬ AdianRabinWordProblem.wordProblemPred x) ≤₀ NonMFCode :=
  ⟨mfCode_pi02_not_pi01.1, mfCode_pi02_not_pi01.2,
    nonMFCode_sigma02_not_sigma01.1, nonMFCode_sigma02_not_sigma01.2,
    wordProblemCompl_manyOneReduces_nonMF⟩

#audit_closed_axioms GroupApproximation.Full.NN11.mfCode_pi02_not_pi01
#audit_closed_axioms GroupApproximation.Full.NN11.nonMFCode_sigma02_not_sigma01
#audit_closed_axioms GroupApproximation.Full.NN11.notesMFArithmetic

end GroupApproximation.Full.NN11
