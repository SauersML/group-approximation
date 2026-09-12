import GroupApproximation.Computability.MFRecognitionWordDefectPrimrec

/-! # Primitive-recursive bounded MF certificate packets -/

namespace GroupApproximation
namespace MFRecognitionPi02

open Nat.Partrec
open PresentationCodes RawWord RawTransformPrimrec
open EffectiveMatrixCode EffectiveMatrixCodePrimrec
open EffectiveOperatorNormCode EffectiveMicrostateSemantics

noncomputable section

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
      (RawTransformPrimrec.primrec_genCount.comp
        (Primrec.fst.comp Primrec.fst)))
    Primrec.id).of_eq ?_
  intro z
  change (∀ i ∈ List.range (genCount z.1.1),
    isUnitary z.1.2 (generator z.1.2 z.2 i)) ↔
      GeneratorsUnitary z.1.1 z.1.2 z.2
  simp only [GeneratorsUnitary]
  constructor
  · intro h i
    exact h i (List.mem_range.2 i.isLt)
  · intro h i hi
    exact h ⟨i, List.mem_range.1 hi⟩

private abbrev UpperInput :=
  (((PresentationCode × ℕ) × ℕ) × List MatrixCode) × List ℕ

private theorem primrec_upperC :
    Primrec fun p : ℕ × UpperInput => p.2.1.1.1.1 :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
    (Primrec.fst.comp Primrec.snd)))

private theorem primrec_upperD :
    Primrec fun p : ℕ × UpperInput => p.2.1.1.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
    (Primrec.fst.comp Primrec.snd)))

private theorem primrec_upperK :
    Primrec fun p : ℕ × UpperInput => p.2.1.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))

private theorem primrec_upperGenerators :
    Primrec fun p : ℕ × UpperInput => p.2.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)

private theorem primrec_upperRelators :
    Primrec fun p : ℕ × UpperInput => p.2.1.1.1.1.2 :=
  Primrec.snd.comp primrec_upperC

private theorem primrec_upperRelator :
    Primrec fun p : ℕ × UpperInput =>
      p.2.1.1.1.1.2.getD p.1 [] :=
  (Primrec.list_getD ([] : List (ℕ × Bool))).comp
    primrec_upperRelators Primrec.fst

private theorem primrec_upperDefectInput :
    Primrec fun p : ℕ × UpperInput =>
      (((p.2.1.1.1.1, p.2.1.1.1.2), p.2.1.2),
        p.2.1.1.1.1.2.getD p.1 []) :=
  Primrec.pair
    (Primrec.pair (Primrec.pair primrec_upperC primrec_upperD)
      primrec_upperGenerators)
    primrec_upperRelator

private def upperDefectAt (p : ℕ × UpperInput) : MatrixCode :=
  wordDefect p.2.1.1.1.1 p.2.1.1.1.2 p.2.1.2
    (p.2.1.1.1.1.2.getD p.1 [])

private theorem primrec_upperDefect :
    Primrec upperDefectAt := by
  refine (primrec_wordDefect.comp primrec_upperDefectInput).of_eq ?_
  intro p
  rfl

private theorem primrec_upperCert :
    Primrec fun p : ℕ × UpperInput => p.2.2.getD p.1 0 :=
  (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd) Primrec.fst

private def upperNormArgs (p : ℕ × UpperInput) :
    (((ℕ × ℕ) × MatrixCode) × ℕ) :=
  (((p.2.1.1.1.2, p.2.1.1.2), upperDefectAt p), p.2.2.getD p.1 0)

private theorem primrec_upperNormInput :
    Primrec upperNormArgs := by
  refine (Primrec.pair
    (Primrec.pair (Primrec.pair primrec_upperD primrec_upperK)
      primrec_upperDefect)
    primrec_upperCert).of_eq ?_
  intro p
  rfl

private def upperItem (i : ℕ) (z : UpperInput) : Prop :=
  upperNormCert z.1.1.1.2 z.1.1.2 (upperDefectAt (i, z))
    (z.2.getD i 0)

private theorem primrecRel_upperItem :
    PrimrecRel upperItem := by
  refine (primrecPred_upperNormCert.comp primrec_upperNormInput).of_eq ?_
  intro p
  rfl

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_upperPacket :
    PrimrecPred fun z : UpperInput =>
      UpperPacket z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
  have hall : PrimrecRel fun (L : List ℕ) (z : UpperInput) =>
      ∀ i ∈ L, upperItem i z :=
    PrimrecRel.forall_mem_list primrecRel_upperItem
  have hforall : PrimrecPred fun z : UpperInput =>
      ∀ i ∈ List.range z.1.1.1.1.2.length, upperItem i z :=
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
  simp only [UpperPacket, upperItem, upperDefectAt, List.mem_range]

private abbrev LowerInput :=
  (((PresentationCode × List (List (ℕ × Bool))) × ℕ) × List MatrixCode) ×
    List ℕ

private theorem primrec_lowerC :
    Primrec fun p : ℕ × LowerInput => p.2.1.1.1.1 :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
    (Primrec.fst.comp Primrec.snd)))

private theorem primrec_lowerW :
    Primrec fun p : ℕ × LowerInput => p.2.1.1.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
    (Primrec.fst.comp Primrec.snd)))

private theorem primrec_lowerD :
    Primrec fun p : ℕ × LowerInput => p.2.1.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))

private theorem primrec_lowerGenerators :
    Primrec fun p : ℕ × LowerInput => p.2.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)

private theorem primrec_lowerWord :
    Primrec fun p : ℕ × LowerInput =>
      p.2.1.1.1.2.getD p.1 [] :=
  (Primrec.list_getD ([] : List (ℕ × Bool))).comp
    primrec_lowerW Primrec.fst

private theorem primrec_lowerDefectInput :
    Primrec fun p : ℕ × LowerInput =>
      (((p.2.1.1.1.1, p.2.1.1.2), p.2.1.2),
        p.2.1.1.1.2.getD p.1 []) :=
  Primrec.pair
    (Primrec.pair (Primrec.pair primrec_lowerC primrec_lowerD)
      primrec_lowerGenerators)
    primrec_lowerWord

private def lowerDefectAt (p : ℕ × LowerInput) : MatrixCode :=
  wordDefect p.2.1.1.1.1 p.2.1.1.2 p.2.1.2
    (p.2.1.1.1.2.getD p.1 [])

private theorem primrec_lowerDefect :
    Primrec lowerDefectAt := by
  refine (primrec_wordDefect.comp primrec_lowerDefectInput).of_eq ?_
  intro p
  rfl

private theorem primrec_lowerCert :
    Primrec fun p : ℕ × LowerInput => p.2.2.getD p.1 0 :=
  (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd) Primrec.fst

private def lowerNormArgs (p : ℕ × LowerInput) :
    ((ℕ × MatrixCode) × ℕ) :=
  ((p.2.1.1.2, lowerDefectAt p), p.2.2.getD p.1 0)

private theorem primrec_lowerNormInput :
    Primrec lowerNormArgs := by
  refine (Primrec.pair (Primrec.pair primrec_lowerD primrec_lowerDefect)
    primrec_lowerCert).of_eq ?_
  intro p
  rfl

private def lowerItem (i : ℕ) (z : LowerInput) : Prop :=
  lowerThirdCert z.1.1.2 (lowerDefectAt (i, z)) (z.2.getD i 0)

private theorem primrecRel_lowerItem :
    PrimrecRel lowerItem := by
  refine (primrecPred_lowerThirdCert.comp primrec_lowerNormInput).of_eq ?_
  intro p
  rfl

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_lowerPacket :
    PrimrecPred fun z : LowerInput =>
      LowerPacket z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
  have hall : PrimrecRel fun (L : List ℕ) (z : LowerInput) =>
      ∀ i ∈ L, lowerItem i z :=
    PrimrecRel.forall_mem_list primrecRel_lowerItem
  have hforall : PrimrecPred fun z : LowerInput =>
      ∀ i ∈ List.range z.1.1.1.2.length, lowerItem i z :=
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
  simp only [LowerPacket, lowerItem, lowerDefectAt, List.mem_range]

end
end MFRecognitionPi02
end GroupApproximation
