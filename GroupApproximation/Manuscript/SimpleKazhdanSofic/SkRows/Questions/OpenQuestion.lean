import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RankFourEndpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.Questions.AlekseevThom
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Meta.AxiomGuard

/-!
# The finitely presented case, middle sentence (census key `768ac9454e9b`)

`simple_kazhdan_sofic_group.tex`, section `sec:questions` (tex l.733–735):

> Infinite finitely presented simple Kazhdan groups
> exist~\cite{CapraceRemy}, and whether one of them is sofic, or at least
> hyperlinear, remains open.

Before rekeying this clause was part of census key `460d289c5b0f`.

## What is proved and what is not

* **Existence clause** (Caprace–Rémy).  The cited proof uses Kac–Moody lattices in products of twin
  buildings, which the library does not have.  The corpus instead uses `EL_5(L)` over the binary
  Leavitt algebra `L = L_{𝔽₂}(1,2)`.  It is proved to be finitely generated, infinite, simple and
  Kazhdan (`FPSimpleKazhdan.manuscriptSentence_binaryLeavittElementaryInfiniteSimpleKazhdan`).
  Finite presentability is reduced to the existing corpus gap
  `LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement`: `K₂(4, L)` is
  finitely normally generated in `St_4(L)`.  That is true by Khanh (arXiv:2609.08428v1), Theorem 5.4,
  which gives `K₂(4, L) = 1`, but it is not proved in Lean.  The gap is already on disk, so it is
  imported rather than restated.  `manuscriptSentence_fpSimpleKazhdanExist_of_rankFourK2FNG` is the
  `_of_` reduction.
* **"whether one of them is sofic, or at least hyperlinear, remains open"** is a statement about
  the state of knowledge, so it is structural.  The mathematical content behind "or at least" is
  closed here.  `FPSimpleKazhdanSoficQuestion` and `FPSimpleKazhdanHyperlinearQuestion` are the two
  existence questions, and the sofic one implies the hyperlinear one (`isHyperlinear_of_isSofic`).
  A sofic example is not LEF and answers Alekseev–Thom 6.1 (`alekseevThomWitness_of_soficQuestion`,
  which applies the endpoint of `AlekseevThom.lean`).
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.Questions

open GroupApproximation GroupApproximation.SimpleKazhdanSofic

/-- **tex l.733–734**, existence clause, from the corpus rank-four gap: there is an infinite, finitely
presented, simple group with property (T), namely `EL_5(L_{𝔽₂}(1,2))`. -/
theorem manuscriptSentence_fpSimpleKazhdanExist_of_rankFourK2FNG
    (h : GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E :=
  (GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFourK2FinitelyNormallyGenerated
    h).1

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.Questions.manuscriptSentence_fpSimpleKazhdanExist_of_rankFourK2FNG

/-- **The open question of tex l.734**: some infinite, finitely presented, simple Kazhdan group is
sofic.  Not claimed. -/
def FPSimpleKazhdanSoficQuestion : Prop :=
  ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
    HasKazhdanPropertyT.{0, 0} E ∧ IsSofic E

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.Questions.FPSimpleKazhdanSoficQuestion

/-- **The weaker open question of tex l.734–735** ("or at least hyperlinear"): some infinite,
finitely presented, simple Kazhdan group is hyperlinear.  Not claimed. -/
def FPSimpleKazhdanHyperlinearQuestion : Prop :=
  ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
    HasKazhdanPropertyT.{0, 0} E ∧ IsHyperlinear E

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.Questions.FPSimpleKazhdanHyperlinearQuestion

/-- "or at least": a positive answer to the sofic question answers the hyperlinear one, since
sofic groups are hyperlinear. -/
theorem fpSimpleKazhdanHyperlinearQuestion_of_soficQuestion (h : FPSimpleKazhdanSoficQuestion) :
    FPSimpleKazhdanHyperlinearQuestion := by
  obtain ⟨E, _, hinf, hfp, hsimple, hT, hsof⟩ := h
  exact ⟨E, inferInstance, hinf, hfp, hsimple, hT, isHyperlinear_of_isSofic hsof⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.Questions.fpSimpleKazhdanHyperlinearQuestion_of_soficQuestion

/-- A positive answer to the sofic question gives a group that is not LEF and answers Open problem
6.1 of Alekseev–Thom (tex l.735–738). -/
theorem alekseevThomWitness_of_soficQuestion (h : FPSimpleKazhdanSoficQuestion) :
    ∃ (G : Type) (_ : Group G), ¬ IsLEF G ∧ IsAlekseevThomProblemSixOneWitness G := by
  obtain ⟨E, _, _, hfp, _, hT, hsof⟩ := h
  exact ⟨E, inferInstance, manuscriptSentence_soficFPExampleNotLEFAnswersAlekseevThom E hfp hT hsof⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.Questions.alekseevThomWitness_of_soficQuestion

end GroupApproximation.SimpleKazhdanSofic.SkRows.Questions
