import GroupApproximation.Manuscript.NonMFNotes.Full.Arithmetic.MFArithmetic
import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificate

/-!
# The certificate normal form in the proof of `thm:mf-arithmetic`

Manuscript `non_mf_group_notes.tex`, proof of `thm:mf-arithmetic`:

> "At scale `n`, label every word of length at most `n` either by a finite
> normal-closure proof of triviality or by a separation requirement
> `‖w(U)-1‖ ≥ 1/2`, and require relator defect at most `2^{-n-10}`.
> Fixed-dimensional feasibility is decidable over the real closed field.
> Separation-one normalization gives these certificates for MF groups.
> Conversely, … turns a certificate into a weak MF model, and so an MF model.
> Then `P ∈ MF_fp ⟺ ∀ n ∃ c C_MF(P,n,c)`."

Lean reading.
* `mfCode_iff_forall_exists_printedCertificate` is the displayed equivalence,
  unconditionally, for the repository's printed certificates
  `Manuscript.MFRecognition.Certificates.PrintedC`: a certificate at scale `n`
  is a dimension together with a normal-closure derivation for each word it
  labels trivial, and `PrintedC P n c` asks for well-formedness and for unitary
  generators of that dimension with relator defect at most `2^{-n}` and
  separation at least `1/4` on the words labelled nontrivial.  These constants
  are the ones of the repository's certificate route, not the notes'
  `2^{-n-10}` and `1/2`; the equivalence holds for either choice, and only this
  choice is formalized.
* The sentence "Fixed-dimensional feasibility is decidable over the real closed
  field" is Tarski's decision procedure, which is not in Mathlib; the repository
  carries it only as the input structure
  `Certificates.PrintedCertificateInputs`, which this lane does not use.  The
  conclusion it serves, `MF_fp ∈ Π⁰₂` and `NONMF_fp ∈ Σ⁰₂`, is proved
  unconditionally in `Full/Arithmetic/MFArithmetic.lean` through the
  repository's rational matrix checker instead.
-/

namespace GroupApproximation.Full.NN11

open PresentationCodes MFRecognitionSecondLevel

/-- **The certificate normal form** (proof of `thm:mf-arithmetic`,
`non_mf_group_notes.tex`): "Then `P ∈ MF_fp ⟺ ∀ n ∃ c C_MF(P,n,c)`", for the
repository's printed certificates (relator defect `2^{-n}`, separation `1/4`). -/
theorem mfCode_iff_forall_exists_printedCertificate (P : PresentationCode) :
    MFCode P ↔ ∀ n : ℕ, ∃ c : Manuscript.MFRecognition.Certificates.PrintedCertificate,
      Manuscript.MFRecognition.Certificates.PrintedC P n c :=
  Manuscript.MFRecognition.Certificates.isOperatorMF_iff_forall_exists_printedCertificate P

#audit_axioms GroupApproximation.Full.NN11.mfCode_iff_forall_exists_printedCertificate

end GroupApproximation.Full.NN11
