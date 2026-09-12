import GroupApproximation.Computability.MFRecognitionPacketPrimrec

/-! # Primitive-recursive bounded MF answer checker -/

namespace GroupApproximation
namespace MFRecognitionPi02

open Nat.Partrec
open PresentationCodes EffectiveMatrixCode
open CodedMicrostateEncoding EffectiveMicrostateSemantics

noncomputable section

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

end
end MFRecognitionPi02
end GroupApproximation
