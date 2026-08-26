import GroupApproximation.Computability.MFRecognitionCheckerPrimrec

/-!
# A `Π⁰₂` upper bound for Operator-MF recognition

This final module exposes the natural-number checker and the arithmetical-
hierarchy classification. Its matrix, packet, and semantic layers are split
into independently compiled imports.
-/

namespace GroupApproximation
namespace MFRecognitionPi02

open Nat.Partrec ArithmeticalHierarchy
open PresentationCodes AdianRabinWordProblem RawWord
open CodedMicrostateEncoding MFMicrostate

noncomputable section

/-- Both a challenge and its proposed finite answer are total natural-number
decoders. Thus `MFChecker` is an ordinary Boolean matrix on naturals. -/
def MFChecker (c : PresentationCode) (n cert : ℕ) : Bool :=
  answerCheck c (challengeAt n).1 (challengeAt n).2
    (answerCertificateAt cert)

theorem primrec_MFChecker :
    Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      MFChecker z.1.1 z.1.2 z.2 := by
  exact primrec_answerCheck.comp (Primrec.pair
    (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp
          (primrec_challengeAt.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.snd.comp
        (primrec_challengeAt.comp (Primrec.snd.comp Primrec.fst))))
    (primrec_answerCertificateAt.comp Primrec.snd))

theorem computable₂_MFChecker :
    Computable₂ fun z : PresentationCode × ℕ => MFChecker z.1 z.2 :=
  primrec_MFChecker.to_comp.to₂

theorem exists_answerCheck_iff (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) :
    (∃ cert : MFAnswerCertificate, answerCheck c W k cert = true) ↔
      AnswersOpen c W k := by
  constructor
  · rintro ⟨cert, hcert⟩
    cases cert with
    | inl a =>
        exact Or.inl ((exists_voidAnswerCheck_iff c W).1 ⟨a, hcert⟩)
    | inr a =>
        exact Or.inr ((exists_matrixAnswerCheck_iff c W k).1 ⟨a, hcert⟩)
  · rintro (hvoid | hmatrix)
    · obtain ⟨a, ha⟩ := (exists_voidAnswerCheck_iff c W).2 hvoid
      exact ⟨Sum.inl a, ha⟩
    · obtain ⟨a, ha⟩ := (exists_matrixAnswerCheck_iff c W k).2 hmatrix
      exact ⟨Sum.inr a, ha⟩

/-- Decoding the natural answer coordinate loses no witnesses. -/
theorem exists_MFChecker_iff (c : PresentationCode) (n : ℕ) :
    (∃ cert : ℕ, MFChecker c n cert = true) ↔
      AnswersOpen c (challengeAt n).1 (challengeAt n).2 := by
  constructor
  · rintro ⟨cert, hcert⟩
    exact (exists_answerCheck_iff c (challengeAt n).1 (challengeAt n).2).1
      ⟨answerCertificateAt cert, hcert⟩
  · intro h
    obtain ⟨cert, hcert⟩ :=
      (exists_answerCheck_iff c (challengeAt n).1 (challengeAt n).2).2 h
    exact ⟨Encodable.encode cert, by simpa [MFChecker] using hcert⟩

/-- The requested exact `∀∃` checker normal form. -/
theorem isOperatorMF_iff_forall_exists_MFChecker (c : PresentationCode) :
    IsOperatorMF (Carrier c) ↔
      ∀ n, ∃ cert : ℕ, MFChecker c n cert = true := by
  constructor
  · intro h n
    rw [exists_MFChecker_iff]
    exact (isOperatorMF_iff_forall_openAnswers c).1 h
      (challengeAt n).1 (challengeAt n).2
  · intro h
    rw [isOperatorMF_iff_forall_openAnswers]
    intro W k
    have hn := h (Encodable.encode (W, k))
    rw [exists_MFChecker_iff, challengeAt_encode] at hn
    exact hn

/-- For one presentation and one challenge, existence of a finite accepted
answer is recursively enumerable. -/
theorem rePred_MFAnswer :
    REPred fun z : PresentationCode × ℕ =>
      ∃ cert : ℕ, MFChecker z.1 z.2 cert = true :=
  WordProblemRE.rePred_exists_eq_true computable₂_MFChecker

/-- Operator-MF recognition for concrete finite-presentation codes lies in
`Π⁰₂`. This is an upper bound only. -/
theorem operatorMFCode_pi02 :
    Pi02 fun c : PresentationCode => IsOperatorMF (Carrier c) := by
  refine pi02_of_re_family rePred_MFAnswer ?_
  intro c
  exact isOperatorMF_iff_forall_exists_MFChecker c

/-- Non-operator-MF recognition for concrete finite-presentation codes lies in
the second existential level, unconditionally and with the finite checker
above as its witness system. -/
theorem nonOperatorMFCode_sigma02 :
    Sigma02 fun c : PresentationCode => ¬ IsOperatorMF (Carrier c) := by
  exact (sigma02_compl_iff
    (fun c : PresentationCode => IsOperatorMF (Carrier c))).2
    operatorMFCode_pi02

end
end MFRecognitionPi02
end GroupApproximation
