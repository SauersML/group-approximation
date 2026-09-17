import GroupApproximation.Manuscript.SimpleKazhdanSofic.QuestionsClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# The finitely presented case, last sentence (census key `b3fbc4494a6c`)

`simple_kazhdan_sofic_group.tex`, section `sec:questions` (tex l.735–738):

> A sofic example would not be LEF, and it would
> answer Open problem~6.1 of Alekseev and Thom~\cite{AlekseevThom}, which
> asks for finitely presented sofic groups with property~\textup{(T)} that
> are not residually finite.

"A sofic example" refers to the previous sentence (tex l.733–735): an infinite, finitely presented,
simple Kazhdan group that is sofic.  Before rekeying this was census key `816d2ed3585b`.

## Route

* `IsAlekseevThomProblemSixOneWitness G` is the property Open problem 6.1 asks for: `G` is finitely
  presented, sofic, Kazhdan and not residually finite.  The citation itself is credit.
* `manuscriptSentence_soficFPExampleNotLEFAnswersAlekseevThom` is the closed corpus theorem
  `printedSoficKazhdanExampleNotLEF` in this vocabulary.  A finitely presented LEF group is residually
  finite (Stepin / Vershik–Gordon, proved), and an infinite simple group is not (proved).  So the
  example is not LEF and not residually finite, and property (T) is not needed for "not LEF".

Property (T) is taken at universes `{0, 0}` (groups in `Type`, Hilbert spaces in `Type`), as
everywhere else in the corpus.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.Questions

open GroupApproximation GroupApproximation.SimpleKazhdanSofic

/-- **Open problem 6.1 of Alekseev–Thom**, as a property of a group: `G` is finitely presented,
sofic, has property (T), and is not residually finite. -/
def IsAlekseevThomProblemSixOneWitness (G : Type) [Group G] : Prop :=
  Group.IsFinitelyPresented G ∧ IsSofic G ∧ HasKazhdanPropertyT.{0, 0} G ∧ ¬ IsResiduallyFinite G

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.Questions.IsAlekseevThomProblemSixOneWitness

/-- **tex l.735–738.**  Every infinite, finitely presented, simple, sofic group with property (T)
is not LEF, and it answers Open problem 6.1 of Alekseev–Thom. -/
theorem manuscriptSentence_soficFPExampleNotLEFAnswersAlekseevThom :
    ∀ (G : Type) [Group G] [IsSimpleGroup G] [Infinite G], Group.IsFinitelyPresented G →
      HasKazhdanPropertyT.{0, 0} G → IsSofic G →
        ¬ IsLEF G ∧ IsAlekseevThomProblemSixOneWitness G := by
  intro G _ _ _ hfp hT hsof
  obtain ⟨hnotLEF, hwitness⟩ := printedSoficKazhdanExampleNotLEF G hfp hT hsof
  exact ⟨hnotLEF, hwitness⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.Questions.manuscriptSentence_soficFPExampleNotLEFAnswersAlekseevThom

end GroupApproximation.SimpleKazhdanSofic.SkRows.Questions
