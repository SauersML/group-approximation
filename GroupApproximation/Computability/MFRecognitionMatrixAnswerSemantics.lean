import GroupApproximation.Computability.MFRecognitionPerturbation

/-!
# Exact finite matrix-answer semantics for MF recognition
-/

namespace GroupApproximation
namespace MFRecognitionPi02

open PresentationCodes AdianRabinWordProblem RawWord
open EffectiveMatrixCode EffectiveMatrixCodePrimrec
open EffectiveOperatorNormCode
open CodedMicrostateEncoding EffectiveMicrostateSemantics MFMicrostate
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-! ## The finite Boolean matrix checker -/

/-- The executable matrix whose norm is the displacement of a raw word. -/
def wordDefect (c : PresentationCode) (d : ℕ) (gens : List MatrixCode)
    (w : List (ℕ × Bool)) : MatrixCode :=
  matrixSub d (wordMatrix d c.1 gens w) (identity d)

/-- One strict upper certificate for each relator, with exact packet length. -/
def UpperPacket (c : PresentationCode) (d k : ℕ)
    (gens : List MatrixCode) (certs : List ℕ) : Prop :=
  certs.length = c.2.length ∧
    ∀ i < c.2.length,
      upperNormCert d k (wordDefect c d gens (c.2.getD i []))
        (certs.getD i 0)

instance upperPacketDecidable (c : PresentationCode) (d k : ℕ)
    (gens : List MatrixCode) (certs : List ℕ) :
    Decidable (UpperPacket c d k gens certs) := by
  unfold UpperPacket
  infer_instance

/-- One strict lower-third certificate for each tested word, with exact packet
length. -/
def LowerPacket (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (d : ℕ) (gens : List MatrixCode) (certs : List ℕ) : Prop :=
  certs.length = W.length ∧
    ∀ i < W.length,
      lowerThirdCert d (wordDefect c d gens (W.getD i []))
        (certs.getD i 0)

instance lowerPacketDecidable (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (d : ℕ) (gens : List MatrixCode)
    (certs : List ℕ) : Decidable (LowerPacket c W d gens certs) := by
  unfold LowerPacket
  infer_instance

/-- Semantic validity of the finite matrix-answer encoding. -/
def MatrixAnswerValid (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer) : Prop :=
  GeneratorsUnitary c (matrixDimension a) (matrixGenerators a) ∧
    UpperPacket c (matrixDimension a) k (matrixGenerators a)
      (matrixUpperCertificates a) ∧
    LowerPacket c W (matrixDimension a) (matrixGenerators a)
      (matrixLowerCertificates a)

instance matrixAnswerValidDecidable (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer) :
    Decidable (MatrixAnswerValid c W k a) := by
  unfold MatrixAnswerValid
  infer_instance

/-- The complete Boolean matrix branch: exact unitarity, an upper certificate
for every relator, and a lower certificate for every tested word. -/
def matrixAnswerCheck (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer) : Bool :=
  decide (MatrixAnswerValid c W k a)

@[simp] theorem matrixAnswerCheck_eq_true_iff (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer) :
    matrixAnswerCheck c W k a = true ↔ MatrixAnswerValid c W k a := by
  simp [matrixAnswerCheck]

/-- Soundness of one accepted finite matrix answer. -/
theorem openPasses_of_matrixAnswerCheck_eq_true (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer)
    (ha : matrixAnswerCheck c W k a = true) :
    ∃ hunitary : GeneratorsUnitary c (matrixDimension a) (matrixGenerators a),
      PassesOpen c W k
        (toMicrostate c (matrixDimension a) (matrixGenerators a) hunitary) := by
  have hvalid := (matrixAnswerCheck_eq_true_iff c W k a).1 ha
  refine ⟨hvalid.1, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, rfl⟩ := List.get_of_mem hr
    have hcert := hvalid.2.1.2 i.1 i.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2,
      Option.getD_some] at hcert
    rw [toMicrostate_len_eq_matrixSub]
    exact opNorm_lt_invSucc_of_upperNormCert _ _ _ _ hcert
  · intro w hw
    obtain ⟨i, rfl⟩ := List.get_of_mem hw
    have hcert := hvalid.2.2.2 i.1 i.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2,
      Option.getD_some] at hcert
    rw [toMicrostate_len_eq_matrixSub]
    exact one_third_lt_opNorm_of_lowerThirdCert _ _ _ hcert

/-- Completeness of the Boolean matrix branch for an already coded open
microstate packet. -/
theorem exists_matrixAnswerCheck_of_coded_openPasses
    (c : PresentationCode) (W : List (List (ℕ × Bool))) (k d : ℕ)
    (gens : List MatrixCode) (hunitary : GeneratorsUnitary c d gens)
    (hpass : PassesOpen c W k (toMicrostate c d gens hunitary)) :
    ∃ a : MatrixAnswer, matrixAnswerCheck c W k a = true := by
  classical
  have hupp : ∀ i : Fin c.2.length, ∃ m,
      upperNormCert d k (wordDefect c d gens (c.2.get i)) m := by
    intro i
    apply exists_upperNormCert_of_opNorm_lt_invSucc
    rw [wordDefect, ← toMicrostate_len_eq_matrixSub]
    exact hpass.1 (c.2.get i) (List.get_mem c.2 i)
  choose upper hupper using hupp
  have hlow : ∀ i : Fin W.length, ∃ m,
      lowerThirdCert d (wordDefect c d gens (W.get i)) m := by
    intro i
    apply exists_lowerThirdCert_of_one_third_lt_opNorm
    rw [wordDefect, ← toMicrostate_len_eq_matrixSub]
    exact hpass.2 (W.get i) (List.get_mem W i)
  choose lower hlower using hlow
  let upperList : List ℕ := List.ofFn upper
  let lowerList : List ℕ := List.ofFn lower
  let a : MatrixAnswer := (d, (gens, (upperList, lowerList)))
  refine ⟨a, (matrixAnswerCheck_eq_true_iff c W k a).2 ?_⟩
  refine ⟨hunitary, ?_, ?_⟩
  · constructor
    · simp [a, upperList]
    · intro i hi
      have hs : upperList.getD i 0 = upper ⟨i, hi⟩ := by
        simp [upperList, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]
      rw [hs]
      simpa [a, wordDefect, List.getD_eq_getElem?_getD, hi] using
        hupper ⟨i, hi⟩
  · constructor
    · simp [a, lowerList]
    · intro i hi
      have hs : lowerList.getD i 0 = lower ⟨i, hi⟩ := by
        simp [lowerList, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]
      rw [hs]
      simpa [a, wordDefect, List.getD_eq_getElem?_getD, hi] using
        hlower ⟨i, hi⟩

/-- Existential exactness of the finite matrix branch. -/
theorem exists_matrixAnswerCheck_iff (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) :
    (∃ a : MatrixAnswer, matrixAnswerCheck c W k a = true) ↔
      ∃ M : Microstate c, PassesOpen c W k M := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨hunitary, hpass⟩ :=
      openPasses_of_matrixAnswerCheck_eq_true c W k a ha
    exact ⟨toMicrostate c (matrixDimension a) (matrixGenerators a) hunitary,
      hpass⟩
  · rintro ⟨M, hM⟩
    obtain ⟨d, gens, hunitary, hpass⟩ := exists_coded_openPasses M hM
    exact exists_matrixAnswerCheck_of_coded_openPasses
      c W k d gens hunitary hpass

end
end MFRecognitionPi02
end GroupApproximation
