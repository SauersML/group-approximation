import GroupApproximation.Manuscript.NonMFNotes.Full.RadicalArithmetic.Semantics
import GroupApproximation.Computability.MFRecognitionPi02
import GroupApproximation.Computability.WordProblemRE
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-radical-arithmetic`: arithmetic complexity of the MF radical

Manuscript `non_mf_group_notes.tex`, `thm:mf-radical-arithmetic`:

> "Uniformly in a finite presentation `P` and a word `v`,
> `v ∉ Res_MF(G_P)` is `Π⁰₂` and `v ∈ Res_MF(G_P)` is `Σ⁰₂`. The same `Σ⁰₂`
> upper bound holds for the set of radical words after fixing `P`."

The radical `Res_MF(G_P)` is the literal manuscript radical
`manuscriptCoronaMFResidual` of the coded presented group. By
`manuscriptRadicalWordSemantics`, non-membership is
`∀ k, ∃ microstate passing the open test at level k`; the repository's
primitive-recursive matrix-answer checker decides the inner existential over
finite rational answers, so the outer `∀∃` is `Π⁰₂`, and complementation gives
the `Σ⁰₂` bounds.
-/

namespace GroupApproximation.Full.NN02

open ArithmeticalHierarchy PresentationCodes AdianRabinWordProblem MFMicrostate
open CodedMicrostateEncoding

noncomputable section

/-- **`thm:mf-radical-arithmetic`, radical words** (`non_mf_group_notes.tex`):
a pair `(P, v)` of a finite presentation code and a raw word whose value lies
in the MF radical `Res_MF(G_P)`. -/
def RadicalWordCode (p : PresentationCode × List (ℕ × Bool)) : Prop :=
  ev p.1 p.2 ∈ manuscriptCoronaMFResidual (Carrier p.1)

/-- The level-`k` matrix-answer test for the single challenged word `v`. -/
def RadicalCheck (z : (PresentationCode × List (ℕ × Bool)) × ℕ) (a : MatrixAnswer) : Bool :=
  MFRecognitionPi02.matrixAnswerCheck z.1.1 [z.1.2] z.2 a

theorem primrec_radicalCheck :
    Primrec fun y : ((PresentationCode × List (ℕ × Bool)) × ℕ) × MatrixAnswer =>
      RadicalCheck y.1 y.2 := by
  exact MFRecognitionPi02.primrec_matrixAnswerCheck.comp (Primrec.pair
    (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.const [])))
      (Primrec.snd.comp Primrec.fst))
    Primrec.snd)

theorem computable₂_radicalCheck : Computable₂ RadicalCheck :=
  primrec_radicalCheck.to_comp.to₂

theorem rePred_radicalCheck :
    REPred fun z : (PresentationCode × List (ℕ × Bool)) × ℕ =>
      ∃ a : MatrixAnswer, RadicalCheck z a = true :=
  WordProblemRE.rePred_exists_eq_true computable₂_radicalCheck

/-- **`thm:mf-radical-arithmetic`, proof display** (`non_mf_group_notes.tex`),
in checker form: `v ∉ Res_MF(G_P) ⟺ ∀ k ∃ a, check(P, v, k, a)`. -/
theorem not_radicalWordCode_iff (p : PresentationCode × List (ℕ × Bool)) :
    ¬ RadicalWordCode p ↔ ∀ k : ℕ, ∃ a : MatrixAnswer, RadicalCheck (p, k) a = true :=
  (not_mem_manuscriptCoronaMFResidual_iff p.1 p.2).trans
    (forall_congr' fun k => (MFRecognitionPi02.exists_matrixAnswerCheck_iff p.1 [p.2] k).symm)

/-- **`thm:mf-radical-arithmetic`, first clause** (`non_mf_group_notes.tex`):
uniformly in `P` and `v`, `v ∉ Res_MF(G_P)` is `Π⁰₂`. -/
theorem nonRadicalWord_pi02 : Pi02 fun p : PresentationCode × List (ℕ × Bool) =>
    ¬ RadicalWordCode p :=
  pi02_of_re_family rePred_radicalCheck not_radicalWordCode_iff

/-- **`thm:mf-radical-arithmetic`, second clause** (`non_mf_group_notes.tex`):
uniformly in `P` and `v`, `v ∈ Res_MF(G_P)` is `Σ⁰₂`. -/
theorem radicalWord_sigma02 : Sigma02 RadicalWordCode :=
  nonRadicalWord_pi02

/-- The fixed-presentation clause as a closed proposition. -/
def FixedPresentationRadicalSigma02 : Prop :=
  ∀ c : PresentationCode, Sigma02 fun v : List (ℕ × Bool) => RadicalWordCode (c, v)

/-- **`thm:mf-radical-arithmetic`, third clause** (`non_mf_group_notes.tex`):
after fixing `P`, the set of radical words is `Σ⁰₂`. -/
theorem fixedPresentation_radicalWord_sigma02 : FixedPresentationRadicalSigma02 := by
  intro c
  show Pi02 fun v : List (ℕ × Bool) => ¬ RadicalWordCode (c, v)
  have hcomp : Computable₂ fun (z : List (ℕ × Bool) × ℕ) (a : MatrixAnswer) =>
      RadicalCheck ((c, z.1), z.2) a :=
    (primrec_radicalCheck.comp (Primrec.pair
      (Primrec.pair (Primrec.pair (Primrec.const c) (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)).to_comp.to₂
  have hq : REPred fun z : List (ℕ × Bool) × ℕ =>
      ∃ a : MatrixAnswer, RadicalCheck ((c, z.1), z.2) a = true :=
    WordProblemRE.rePred_exists_eq_true hcomp
  exact pi02_of_re_family hq fun v => not_radicalWordCode_iff (c, v)

/-- All three clauses of `thm:mf-radical-arithmetic`, as one closed
proposition. -/
def MFRadicalArithmetic : Prop :=
  Pi02 (fun p : PresentationCode × List (ℕ × Bool) => ¬ RadicalWordCode p) ∧
    Sigma02 RadicalWordCode ∧ FixedPresentationRadicalSigma02

/-- **`thm:mf-radical-arithmetic`** (`non_mf_group_notes.tex`), closed. -/
theorem manuscriptMFRadicalArithmetic : MFRadicalArithmetic :=
  ⟨nonRadicalWord_pi02, radicalWord_sigma02, fixedPresentation_radicalWord_sigma02⟩

end

#audit_closed_axioms GroupApproximation.Full.NN02.nonRadicalWord_pi02
#audit_closed_axioms GroupApproximation.Full.NN02.radicalWord_sigma02
#audit_closed_axioms GroupApproximation.Full.NN02.fixedPresentation_radicalWord_sigma02
#audit_closed_axioms GroupApproximation.Full.NN02.manuscriptMFRadicalArithmetic

end GroupApproximation.Full.NN02
