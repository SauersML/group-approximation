import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.ToRealFormula
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.Decide
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.Spec
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.PrimrecFormula
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.WellFormed.Decide
import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificate
import GroupApproximation.Manuscript.NonMFNotes.Full.Arithmetic.MFArithmetic

/-!
# The printed-certificate route of `thm:mf-arithmetic`, unconditionally

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field", and `prop:mf-upper-bound`,
printed sentences `9eae4d68673a` ("`Φ(P,n,c)` is a sentence of the first-order theory of
the ordered field of real numbers") and `a5c1cde4d5f1` (Tarski: its truth is decidable).

The repository's `PrintedCertificateInputs` is built here with no hypotheses:

* `encode` is the prenex sentence `encodePrenex` (lane NN11bH), printed as a
  `RealFormula` through `prenexFormula`;
* the Tarski decision of `encode z` agrees with `decidePrenex (encodePrenex z)`
  (`decidePrenex_iff_holds`), which is computable (lanes NN11bF, NN11bH);
* the well-formedness check is the repository's decision (lane NN11bG).

So `MF_fp ∈ Π⁰₂` and `NONMF_fp ∈ Σ⁰₂` follow along the printed route
(`printedCertificatesUpperBound_tarski`).
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes Manuscript.MFRecognition.Certificates
open ArithmeticalHierarchy

/-- Truth at the zero assignment, decided classically.  Computability is not claimed for
this map itself; only its composite with `encode` is shown computable, through
`decidePrenex`. -/
noncomputable def tarskiInput : TarskiInput where
  decideFormula φ := @decide (φ.Holds fun _ => 0) (Classical.propDecidable _)
  decideFormula_iff φ := @decide_eq_true_iff _ (Classical.propDecidable _)

/-- The sentence `Φ(P, n, c)` as a printed real formula. -/
noncomputable def encodeFormula (z : (PresentationCode × ℕ) × PrintedCertificate) :
    RealFormula :=
  prenexFormula (encodePrenex z).1 (encodePrenex z).2

theorem encodeFormula_spec (P : PresentationCode) (n : ℕ) (c : PrintedCertificate) :
    ((encodeFormula ((P, n), c)).Holds fun _ => 0) ↔ PhiSpec P n c :=
  (holds_prenexFormula _ _ _).trans (encodePrenex_spec P n c)

theorem decidePrenex_encodePrenex_eq (z : (PresentationCode × ℕ) × PrintedCertificate) :
    decidePrenex (encodePrenex z) = tarskiInput.decideFormula (encodeFormula z) :=
  Bool.eq_iff_iff.2 ((decidePrenex_iff_holds (encodePrenex z)).trans
    (@decide_eq_true_iff _ (Classical.propDecidable _)).symm)

/-- **`PrintedCertificateInputs`, unconditionally.** -/
noncomputable def printedCertificateInputs : PrintedCertificateInputs where
  tarski := tarskiInput
  encode := encodeFormula
  encode_spec := encodeFormula_spec
  phiDecision_computable :=
    (computable_decidePrenex.comp computable_encodePrenex).of_eq decidePrenex_encodePrenex_eq
  wellFormedCheck z := decide (WellFormed z.1.1 z.1.2 z.2)
  wellFormedCheck_computable := computable_wellFormedDecide
  wellFormedCheck_spec := fun P n c => @decide_eq_true_iff (WellFormed P n c) _

/-- **`prop:mf-upper-bound` along the printed Tarski route**: `MF_fp ∈ Π⁰₂` and
`NONMF_fp ∈ Σ⁰₂`, with no hypotheses. -/
theorem printedCertificatesUpperBound_tarski :
    Pi02 (fun P : PresentationCode => P ∈ MFfp) ∧
      Sigma02 fun P : PresentationCode => P ∈ NONMFfp :=
  printedCertificatesUpperBound printedCertificateInputs

/-- **`thm:mf-arithmetic`, with the printed proof step.**  The upper bounds are obtained
along the printed route (feasibility of fixed-dimensional systems is decidable over
the reals), together with lane NN11's `notesMFArithmetic`. -/
theorem notesMFArithmetic_tarski :
    (Pi02 (fun P : PresentationCode => P ∈ MFfp) ∧
      Sigma02 fun P : PresentationCode => P ∈ NONMFfp) ∧
    (Pi02 MFRecognitionSecondLevel.MFCode ∧ ¬ Pi01 MFRecognitionSecondLevel.MFCode ∧
      Sigma02 MFRecognitionSecondLevel.NonMFCode ∧
      ¬ Sigma01 MFRecognitionSecondLevel.NonMFCode ∧
      (fun x => ¬ AdianRabinWordProblem.wordProblemPred x) ≤₀
        MFRecognitionSecondLevel.NonMFCode) :=
  ⟨printedCertificatesUpperBound_tarski, NN11.notesMFArithmetic⟩

end GroupApproximation.Full.NN11b
