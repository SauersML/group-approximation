import GroupApproximation.Computability.MFRecognitionMatrixAnswerSemantics

/-!
# Primitive-recursive coding of MF word defects

This small module isolates the matrix-word composition used by the bounded
checker, keeping projection inference out of the larger packet proofs.
-/

namespace GroupApproximation
namespace MFRecognitionPi02

open Nat.Partrec
open PresentationCodes EffectiveMatrixCode EffectiveMatrixCodePrimrec

noncomputable section

private abbrev WordDefectInput :=
  (((PresentationCode × ℕ) × List MatrixCode) × List (ℕ × Bool))

private theorem primrec_wordMatrixForPresentation :
    Primrec fun z : WordDefectInput =>
      wordMatrix z.1.1.2 z.1.1.1.1 z.1.2 z.2 := by
  have hc : Primrec fun z : WordDefectInput => z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hd : Primrec fun z : WordDefectInput => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hgens : Primrec fun z : WordDefectInput => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec fun z : WordDefectInput => z.2 := Primrec.snd
  have hcGenerators : Primrec fun z : WordDefectInput => z.1.1.1.1 :=
    Primrec.fst.comp hc
  exact primrec_wordMatrix.comp
    (Primrec.pair (Primrec.pair (Primrec.pair hd hcGenerators) hgens) hw)

private theorem primrec_identityForPresentation :
    Primrec fun z : WordDefectInput => identity z.1.1.2 := by
  have hd : Primrec fun z : WordDefectInput => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  exact primrec_identity.comp hd

theorem primrec_wordDefect :
    Primrec fun z : WordDefectInput =>
      wordDefect z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  change Primrec fun z : WordDefectInput =>
    matrixSub z.1.1.2
      (wordMatrix z.1.1.2 z.1.1.1.1 z.1.2 z.2) (identity z.1.1.2)
  have hid : Primrec fun z : WordDefectInput => identity z.1.1.2 :=
    primrec_identityForPresentation
  have hword : Primrec fun z : WordDefectInput =>
      wordMatrix z.1.1.2 z.1.1.1.1 z.1.2 z.2 :=
    primrec_wordMatrixForPresentation
  have hd : Primrec fun z : WordDefectInput => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  exact primrec_matrixSub.comp
    (Primrec.pair (Primrec.pair hd hword) hid)

end
end MFRecognitionPi02
end GroupApproximation
