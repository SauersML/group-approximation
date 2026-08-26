import GroupApproximation.Computability.MFRecognitionMatrixAnswerSemantics

/-!
# A `Π⁰₂` upper bound for Operator-MF recognition

This final module audits the bounded exact checker and states the arithmetical-
hierarchy classification; semantic and perturbation layers are imported from
smaller independently compiled modules.
-/

namespace GroupApproximation
namespace MFRecognitionPi02

open Nat.Partrec ArithmeticalHierarchy
open PresentationCodes AdianRabinWordProblem RawWord
open EffectiveMatrixCode EffectiveMatrixCodePrimrec
open EffectiveOperatorNormCode CodedMicrostateEncoding
open EffectiveMicrostateSemantics MFMicrostate
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-! ## Primitive recursiveness of the bounded exact checks -/

theorem primrec_wordDefect :
    Primrec fun z : (((PresentationCode × ℕ) × List MatrixCode) ×
      List (ℕ × Bool)) =>
      wordDefect z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hword : Primrec fun z : (((PresentationCode × ℕ) × List MatrixCode) ×
      List (ℕ × Bool)) =>
      wordMatrix z.1.1.2 z.1.1.1.1 z.1.2 z.2 :=
    primrec_wordMatrix.comp (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  exact primrec_matrixSub.comp (Primrec.pair
    (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      hword)
    (primrec_identity.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_generatorsUnitary :
    PrimrecPred fun z : (PresentationCode × ℕ) × List MatrixCode =>
      GeneratorsUnitary z.1.1 z.1.2 z.2 := by
  have hitem : PrimrecRel fun (i : ℕ)
      (z : (PresentationCode × ℕ) × List MatrixCode) =>
      isUnitary z.1.2 (generator z.1.2 z.2 i) := by
    exact EffectiveMatrixCodePrimrec.primrecPred_isUnitary.comp (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (primrec_generator.comp (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)) Primrec.fst)))
  have hall : PrimrecRel fun (L : List ℕ)
      (z : (PresentationCode × ℕ) × List MatrixCode) =>
      ∀ i ∈ L, isUnitary z.1.2 (generator z.1.2 z.2 i) :=
    PrimrecRel.forall_mem_list hitem
  refine (hall.comp
    (Primrec.list_range.comp
      (primrec_genCount.comp (Primrec.fst.comp Primrec.fst)))
    Primrec.id).of_eq ?_
  intro z
  constructor
  · intro h i
    exact h i (List.mem_range.2 i.isLt)
  · intro h i hi
    exact h ⟨i, List.mem_range.1 hi⟩

private abbrev UpperInput :=
  (((PresentationCode × ℕ) × ℕ) × List MatrixCode) × List ℕ

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_upperPacket :
    PrimrecPred fun z : UpperInput =>
      UpperPacket z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
  have hitem : PrimrecRel fun (i : ℕ) (z : UpperInput) =>
      upperNormCert z.1.1.1.2 z.1.1.2
        (wordDefect z.1.1.1.1 z.1.1.1.2 z.1.2
          (z.1.1.1.1.2.getD i []))
        (z.2.getD i 0) := by
    have hc : Primrec fun p : ℕ × UpperInput => p.2.1.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd)))
    have hd : Primrec fun p : ℕ × UpperInput => p.2.1.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd)))
    have hk : Primrec fun p : ℕ × UpperInput => p.2.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    have hgens : Primrec fun p : ℕ × UpperInput => p.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hrels : Primrec fun p : ℕ × UpperInput => p.2.1.1.1.1.2 :=
      Primrec.snd.comp hc
    have hrelator : Primrec fun p : ℕ × UpperInput =>
        p.2.1.1.1.1.2.getD p.1 [] :=
      (Primrec.list_getD ([] : List (ℕ × Bool))).comp hrels Primrec.fst
    have hdefect : Primrec fun p : ℕ × UpperInput =>
        wordDefect p.2.1.1.1.1 p.2.1.1.1.2 p.2.1.2
          (p.2.1.1.1.1.2.getD p.1 []) :=
      primrec_wordDefect.comp (Primrec.pair
        (Primrec.pair (Primrec.pair hc hd) hgens) hrelator)
    have hcert : Primrec fun p : ℕ × UpperInput => p.2.2.getD p.1 0 :=
      (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd) Primrec.fst
    exact primrecPred_upperNormCert.comp (Primrec.pair
      (Primrec.pair (Primrec.pair hd hk) hdefect) hcert)
  have hall : PrimrecRel fun (L : List ℕ) (z : UpperInput) =>
      ∀ i ∈ L,
        upperNormCert z.1.1.1.2 z.1.1.2
          (wordDefect z.1.1.1.1 z.1.1.1.2 z.1.2
            (z.1.1.1.1.2.getD i []))
          (z.2.getD i 0) :=
    PrimrecRel.forall_mem_list hitem
  have hforall : PrimrecPred fun z : UpperInput =>
      ∀ i ∈ List.range z.1.1.1.1.2.length,
        upperNormCert z.1.1.1.2 z.1.1.2
          (wordDefect z.1.1.1.1 z.1.1.1.2 z.1.2
            (z.1.1.1.1.2.getD i []))
          (z.2.getD i 0) :=
    hall.comp
      (Primrec.list_range.comp (Primrec.list_length.comp
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst))))))
      Primrec.id
  have hlen : PrimrecPred fun z : UpperInput =>
      z.2.length = z.1.1.1.1.2.length :=
    Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
  refine (PrimrecPred.and hlen hforall).of_eq ?_
  intro z
  simp only [UpperPacket]
  constructor
  · rintro ⟨hlen', h⟩
    exact ⟨hlen', fun i hi => h i (List.mem_range.2 hi)⟩
  · rintro ⟨hlen', h⟩
    exact ⟨hlen', fun i hi => h i (List.mem_range.1 hi)⟩

private abbrev LowerInput :=
  (((PresentationCode × List (List (ℕ × Bool))) × ℕ) × List MatrixCode) ×
    List ℕ

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_lowerPacket :
    PrimrecPred fun z : LowerInput =>
      LowerPacket z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
  have hitem : PrimrecRel fun (i : ℕ) (z : LowerInput) =>
      lowerThirdCert z.1.1.2
        (wordDefect z.1.1.1.1 z.1.1.2 z.1.2
          (z.1.1.1.2.getD i []))
        (z.2.getD i 0) := by
    have hc : Primrec fun p : ℕ × LowerInput => p.2.1.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd)))
    have hW : Primrec fun p : ℕ × LowerInput => p.2.1.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd)))
    have hd : Primrec fun p : ℕ × LowerInput => p.2.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    have hgens : Primrec fun p : ℕ × LowerInput => p.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hword : Primrec fun p : ℕ × LowerInput =>
        p.2.1.1.1.2.getD p.1 [] :=
      (Primrec.list_getD ([] : List (ℕ × Bool))).comp hW Primrec.fst
    have hdefect : Primrec fun p : ℕ × LowerInput =>
        wordDefect p.2.1.1.1.1 p.2.1.1.2 p.2.1.2
          (p.2.1.1.1.2.getD p.1 []) :=
      primrec_wordDefect.comp (Primrec.pair
        (Primrec.pair (Primrec.pair hc hd) hgens) hword)
    have hcert : Primrec fun p : ℕ × LowerInput => p.2.2.getD p.1 0 :=
      (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd) Primrec.fst
    exact primrecPred_lowerThirdCert.comp
      (Primrec.pair (Primrec.pair hd hdefect) hcert)
  have hall : PrimrecRel fun (L : List ℕ) (z : LowerInput) =>
      ∀ i ∈ L,
        lowerThirdCert z.1.1.2
          (wordDefect z.1.1.1.1 z.1.1.2 z.1.2
            (z.1.1.1.2.getD i []))
          (z.2.getD i 0) :=
    PrimrecRel.forall_mem_list hitem
  have hforall : PrimrecPred fun z : LowerInput =>
      ∀ i ∈ List.range z.1.1.1.2.length,
        lowerThirdCert z.1.1.2
          (wordDefect z.1.1.1.1 z.1.1.2 z.1.2
            (z.1.1.1.2.getD i []))
          (z.2.getD i 0) :=
    hall.comp
      (Primrec.list_range.comp (Primrec.list_length.comp
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst))))) Primrec.id
  have hlen : PrimrecPred fun z : LowerInput =>
      z.2.length = z.1.1.1.2.length :=
    Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.fst))))
  refine (PrimrecPred.and hlen hforall).of_eq ?_
  intro z
  simp only [LowerPacket]
  constructor
  · rintro ⟨hlen', h⟩
    exact ⟨hlen', fun i hi => h i (List.mem_range.2 hi)⟩
  · rintro ⟨hlen', h⟩
    exact ⟨hlen', fun i hi => h i (List.mem_range.1 hi)⟩

private abbrev MatrixCheckInput :=
  ((PresentationCode × List (List (ℕ × Bool))) × ℕ) × MatrixAnswer

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_matrixAnswerValid :
    PrimrecPred fun z : MatrixCheckInput =>
      MatrixAnswerValid z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hc : Primrec fun z : MatrixCheckInput => z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hW : Primrec fun z : MatrixCheckInput => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec fun z : MatrixCheckInput => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hd : Primrec fun z : MatrixCheckInput => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hgens : Primrec fun z : MatrixCheckInput => z.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hupp : Primrec fun z : MatrixCheckInput => z.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hlow : Primrec fun z : MatrixCheckInput => z.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hunit : PrimrecPred fun z : MatrixCheckInput =>
      GeneratorsUnitary z.1.1.1 z.2.1 z.2.2.1 :=
    primrecPred_generatorsUnitary.comp
      (Primrec.pair (Primrec.pair hc hd) hgens)
  have hupper : PrimrecPred fun z : MatrixCheckInput =>
      UpperPacket z.1.1.1 z.2.1 z.1.2 z.2.2.1 z.2.2.2.1 :=
    primrecPred_upperPacket.comp (Primrec.pair
      (Primrec.pair (Primrec.pair (Primrec.pair hc hd) hk) hgens) hupp)
  have hlower : PrimrecPred fun z : MatrixCheckInput =>
      LowerPacket z.1.1.1 z.1.1.2 z.2.1 z.2.2.1 z.2.2.2.2 :=
    primrecPred_lowerPacket.comp (Primrec.pair
      (Primrec.pair (Primrec.pair (Primrec.pair hc hW) hd) hgens) hlow)
  exact PrimrecPred.and hunit (PrimrecPred.and hupper hlower)

theorem primrec_matrixAnswerCheck :
    Primrec fun z : MatrixCheckInput =>
      matrixAnswerCheck z.1.1.1 z.1.1.2 z.1.2 z.2 :=
  primrecPred_matrixAnswerValid.decide

/-! ## The full checker and the hierarchy upper bound -/

/-- Combine the executable void and matrix branches for one challenge. -/
def answerCheck (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (k : ℕ) : MFAnswerCertificate → Bool
  | Sum.inl a => voidAnswerCheck c W a
  | Sum.inr a => matrixAnswerCheck c W k a

theorem primrec_answerCheck :
    Primrec fun z : ((PresentationCode × List (List (ℕ × Bool))) × ℕ) ×
      MFAnswerCertificate => answerCheck z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hvoid : Primrec₂ fun
      (z : ((PresentationCode × List (List (ℕ × Bool))) × ℕ) ×
        MFAnswerCertificate) (a : VoidAnswer) =>
      voidAnswerCheck z.1.1.1 z.1.1.2 a := by
    exact (primrec_voidAnswerCheck.comp (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd)).to₂
  have hmatrix : Primrec₂ fun
      (z : ((PresentationCode × List (List (ℕ × Bool))) × ℕ) ×
        MFAnswerCertificate) (a : MatrixAnswer) =>
      matrixAnswerCheck z.1.1.1 z.1.1.2 z.1.2 a := by
    exact (primrec_matrixAnswerCheck.comp (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)).to₂
  exact (Primrec.sumCasesOn Primrec.snd hvoid hmatrix).of_eq fun z => by
    cases z.2 <;> rfl

/-- Both a challenge and its proposed finite answer are total natural-number
decoders.  Thus `MFChecker` is an ordinary Boolean matrix on naturals. -/
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
  rw [isOperatorMF_iff_forall_openAnswers]
  rw [← forall_challengeAt_iff]
  apply forall_congr'
  intro n
  exact (exists_MFChecker_iff c n).symm

/-- For one presentation and one challenge, existence of a finite accepted
answer is recursively enumerable. -/
theorem rePred_MFAnswer :
    REPred fun z : PresentationCode × ℕ =>
      ∃ cert : ℕ, MFChecker z.1 z.2 cert = true :=
  WordProblemRE.rePred_exists_eq_true computable₂_MFChecker

/-- Operator-MF recognition for concrete finite-presentation codes lies in
`Π⁰₂`.  This is an upper bound only. -/
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
