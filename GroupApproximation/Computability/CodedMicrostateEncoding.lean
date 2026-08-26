import GroupApproximation.Computability.RationalMatrixEncoding
import GroupApproximation.Computability.WordProblemRE

/-!
# Finite codes for the MF `\Pi^0_2` checker

This file contains only the discrete encoding layer of the finite-presentation
MF upper bound.  A challenge is a finite list of raw words and a precision
index.  An answer is either a word-problem certificate showing that the
challenge is vacuous, or finite Gaussian-rational matrix data together with
natural-number norm certificates.

All types are built from primitive-recursive datatypes.  The natural-number
decoders are totalized by explicit defaults and are proved primitive recursive.
The void branch is already executable and its exact semantics follows from the
repository's raw word-problem search.  The matrix branch is deliberately only
encoded here: its checker belongs to the effective operator-norm certificate
layer.
-/

namespace GroupApproximation
namespace CodedMicrostateEncoding

open PresentationCodes EffectiveMatrixCode

/-- A presentation-independent word code. -/
abbrev RawWord : Type := List (ℕ × Bool)

/-- A finite MF challenge: tested words and the reciprocal precision index. -/
abbrev Challenge : Type := List RawWord × ℕ

/-- A finite matrix answer.  Its fields are, in order: the dimension offset,
the generator matrices, one upper-norm certificate per relator, and one
lower-norm certificate per tested word. -/
abbrev MatrixAnswer : Type :=
  ℕ × (List MatrixCode × (List ℕ × List ℕ))

/-- A proof that a challenge is vacuous: a challenged word and a raw
word-problem search certificate for it. -/
abbrev VoidAnswer : Type := RawWord × WordProblemRE.SearchData

/-- The finite answer type used by the eventual packet checker. -/
abbrev MFAnswerCertificate : Type := VoidAnswer ⊕ MatrixAnswer

example : Primcodable Challenge := inferInstance
example : Primcodable MatrixAnswer := inferInstance
example : Primcodable VoidAnswer := inferInstance
example : Primcodable MFAnswerCertificate := inferInstance

/-! ## Explicit defaults and total natural-number decoders -/

def defaultChallenge : Challenge := ([], 0)

def defaultMatrixAnswer : MatrixAnswer := (0, ([], ([], [])))

def defaultVoidAnswer : VoidAnswer := ([], ([], []))

def defaultMFAnswerCertificate : MFAnswerCertificate :=
  Sum.inl defaultVoidAnswer

/-- Every natural number denotes a challenge; malformed codes denote the
explicit empty challenge. -/
def challengeAt (n : ℕ) : Challenge :=
  (Encodable.decode (α := Challenge) n).getD defaultChallenge

/-- Every natural number denotes a matrix answer. -/
def matrixAnswerAt (n : ℕ) : MatrixAnswer :=
  (Encodable.decode (α := MatrixAnswer) n).getD defaultMatrixAnswer

/-- Every natural number denotes a void answer. -/
def voidAnswerAt (n : ℕ) : VoidAnswer :=
  (Encodable.decode (α := VoidAnswer) n).getD defaultVoidAnswer

/-- Every natural number denotes a complete answer certificate. -/
def answerCertificateAt (n : ℕ) : MFAnswerCertificate :=
  (Encodable.decode (α := MFAnswerCertificate) n).getD
    defaultMFAnswerCertificate

theorem primrec_challengeAt : Primrec challengeAt :=
  Primrec.option_getD.comp (@Primrec.decode Challenge _)
    (Primrec.const defaultChallenge)

theorem primrec_matrixAnswerAt : Primrec matrixAnswerAt :=
  Primrec.option_getD.comp (@Primrec.decode MatrixAnswer _)
    (Primrec.const defaultMatrixAnswer)

theorem primrec_voidAnswerAt : Primrec voidAnswerAt :=
  Primrec.option_getD.comp (@Primrec.decode VoidAnswer _)
    (Primrec.const defaultVoidAnswer)

theorem primrec_answerCertificateAt : Primrec answerCertificateAt :=
  Primrec.option_getD.comp (@Primrec.decode MFAnswerCertificate _)
    (Primrec.const defaultMFAnswerCertificate)

theorem computable_challengeAt : Computable challengeAt :=
  primrec_challengeAt.to_comp

theorem computable_matrixAnswerAt : Computable matrixAnswerAt :=
  primrec_matrixAnswerAt.to_comp

theorem computable_voidAnswerAt : Computable voidAnswerAt :=
  primrec_voidAnswerAt.to_comp

theorem computable_answerCertificateAt : Computable answerCertificateAt :=
  primrec_answerCertificateAt.to_comp

@[simp] theorem challengeAt_encode (q : Challenge) :
    challengeAt (Encodable.encode q) = q := by
  simp [challengeAt, Encodable.encodek]

@[simp] theorem matrixAnswerAt_encode (a : MatrixAnswer) :
    matrixAnswerAt (Encodable.encode a) = a := by
  simp [matrixAnswerAt, Encodable.encodek]

@[simp] theorem voidAnswerAt_encode (a : VoidAnswer) :
    voidAnswerAt (Encodable.encode a) = a := by
  simp [voidAnswerAt, Encodable.encodek]

@[simp] theorem answerCertificateAt_encode (a : MFAnswerCertificate) :
    answerCertificateAt (Encodable.encode a) = a := by
  simp [answerCertificateAt, Encodable.encodek]

theorem challengeAt_surjective : Function.Surjective challengeAt :=
  fun q => ⟨Encodable.encode q, challengeAt_encode q⟩

theorem matrixAnswerAt_surjective : Function.Surjective matrixAnswerAt :=
  fun a => ⟨Encodable.encode a, matrixAnswerAt_encode a⟩

theorem voidAnswerAt_surjective : Function.Surjective voidAnswerAt :=
  fun a => ⟨Encodable.encode a, voidAnswerAt_encode a⟩

theorem answerCertificateAt_surjective :
    Function.Surjective answerCertificateAt :=
  fun a => ⟨Encodable.encode a, answerCertificateAt_encode a⟩

/-- Quantifying over natural-number challenge codes is exactly quantifying over
all finite word packets and precision indices. -/
theorem forall_challengeAt_iff {p : Challenge → Prop} :
    (∀ n, p (challengeAt n)) ↔ ∀ W k, p (W, k) := by
  constructor
  · intro h W k
    simpa using h (Encodable.encode (W, k))
  · intro h n
    exact h (challengeAt n).1 (challengeAt n).2

/-! ## Named projections from the product encodings -/

def challengeWords (q : Challenge) : List RawWord := q.1

def challengeScale (q : Challenge) : ℕ := q.2

def matrixDimension (a : MatrixAnswer) : ℕ := a.1

def matrixGenerators (a : MatrixAnswer) : List MatrixCode := a.2.1

def matrixUpperCertificates (a : MatrixAnswer) : List ℕ := a.2.2.1

def matrixLowerCertificates (a : MatrixAnswer) : List ℕ := a.2.2.2

def voidWord (a : VoidAnswer) : RawWord := a.1

def voidSearchData (a : VoidAnswer) : WordProblemRE.SearchData := a.2

theorem primrec_challengeWords : Primrec challengeWords := Primrec.fst

theorem primrec_challengeScale : Primrec challengeScale := Primrec.snd

theorem primrec_matrixDimension : Primrec matrixDimension := Primrec.fst

theorem primrec_matrixGenerators : Primrec matrixGenerators :=
  Primrec.fst.comp Primrec.snd

theorem primrec_matrixUpperCertificates :
    Primrec matrixUpperCertificates :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

theorem primrec_matrixLowerCertificates :
    Primrec matrixLowerCertificates :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

theorem primrec_voidWord : Primrec voidWord := Primrec.fst

theorem primrec_voidSearchData : Primrec voidSearchData := Primrec.snd

/-! ## The executable void branch -/

/-- Accept a void answer precisely when it selects a challenged word and its
raw search data proves that word trivial in the presented group. -/
def voidAnswerCheck (P : PresentationCode) (W : List RawWord)
    (a : VoidAnswer) : Bool :=
  decide (a.1 ∈ W) && WordProblemRE.searchCheck (P, a.1) a.2

/-- Exact semantics of the void branch.  No group-theoretic oracle occurs in
the Boolean checker: the equality is witnessed by `WordProblemRE.SearchData`.
-/
theorem exists_voidAnswerCheck_iff (P : PresentationCode) (W : List RawWord) :
    (∃ a, voidAnswerCheck P W a = true) ↔
      ∃ w ∈ W, AdianRabinWordProblem.WordProblem P w := by
  constructor
  · rintro ⟨⟨w, search⟩, h⟩
    simp only [voidAnswerCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hw : AdianRabinWordProblem.wordProblemPred (P, w) :=
      (WordProblemRE.wordProblemPred_iff_exists (P, w)).2
        ⟨search, h.2⟩
    exact ⟨w, h.1, by
      simpa [AdianRabinWordProblem.wordProblemPred] using hw⟩
  · rintro ⟨w, hwW, hw⟩
    have hw' : AdianRabinWordProblem.wordProblemPred (P, w) := by
      simpa [AdianRabinWordProblem.wordProblemPred] using hw
    obtain ⟨search, hsearch⟩ :=
      (WordProblemRE.wordProblemPred_iff_exists (P, w)).1 hw'
    exact ⟨(w, search), by simp [voidAnswerCheck, hwW, hsearch]⟩

/-- The challenged-word membership test is primitive recursive uniformly in
the finite packet. -/
theorem primrecPred_voidWordMem :
    PrimrecPred fun z : (PresentationCode × List RawWord) × VoidAnswer =>
      z.2.1 ∈ z.1.2 := by
  have h : PrimrecRel fun (L : List RawWord) (w : RawWord) =>
      ∃ u ∈ L, u = w := PrimrecRel.exists_mem_list Primrec.eq
  refine (h.comp (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)).of_eq fun z => ?_
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hz
    exact ⟨z.2.1, hz, rfl⟩

/-- The complete void checker is primitive recursive in the presentation,
challenge packet, and answer. -/
theorem primrec_voidAnswerCheck :
    Primrec fun z : (PresentationCode × List RawWord) × VoidAnswer =>
      voidAnswerCheck z.1.1 z.1.2 z.2 := by
  have hsearch :
      Primrec fun z : (PresentationCode × List RawWord) × VoidAnswer =>
        WordProblemRE.searchCheck (z.1.1, z.2.1) z.2.2 :=
    WordProblemRE.primrec_searchCheck.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.and.comp primrecPred_voidWordMem.decide hsearch).of_eq
    fun _ => rfl

theorem computable_voidAnswerCheck :
    Computable fun z : (PresentationCode × List RawWord) × VoidAnswer =>
      voidAnswerCheck z.1.1 z.1.2 z.2 :=
  primrec_voidAnswerCheck.to_comp

end CodedMicrostateEncoding
end GroupApproximation
