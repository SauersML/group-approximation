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

end
end MFRecognitionPi02
end GroupApproximation
