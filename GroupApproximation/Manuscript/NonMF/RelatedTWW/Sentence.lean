import GroupApproximation.Manuscript.NonMF.RelatedTWW.Elementary
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Tikuisis--White--Winter): the printed sentence

Census row `82cac0c03a39`, `non_mf_groups_exist.tex` L315--318 (Related work,
paragraph starting at L310):

> It also asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal; for algebras that satisfy the universal coefficient theorem
> and have a faithful trace, the theorem of Tikuisis, White, and Winter recalled
> above answers this~\cite{TWW}.

The theorem recalled above, at L279--281:

> Tikuisis, White, and Winter proved that faithful traces on separable nuclear
> $C^*$-algebras satisfying the universal coefficient theorem are
> quasidiagonal~\cite{TWW}

## What is proved, and what is isolated

Proved unconditionally:

* `manuscriptSentence_quasidiagonalImpliesStablyFinite` and
  `manuscriptSentence_quasidiagonalImpliesMF`. Quasidiagonal algebras are MF,
  hence stably finite.
* `manuscriptSentence_blackadarKirchbergQuestion_iff`. The printed question is
  the converse, so it is equivalent to "stably finite ↔ quasidiagonal" for
  separable nuclear algebras.
* `manuscriptSentence_faithfulTraceStablyFinite`. A faithful trace forces stable
  finiteness, so the class of L317 lies inside the class the question is about.
* `manuscriptSentence_quasidiagonal_of_faithful_quasidiagonalTrace`. A faithful
  quasidiagonal trace makes the algebra quasidiagonal (Brown's argument). This
  is the step from the recalled theorem to "answers this".

Isolated: the recalled theorem itself, `TikuisisWhiteWinterStatement T`, with
the UCT read in the Kasparov theory `T` as `T.SatisfiesUCT`. From it,
`manuscriptSentence_blackadarKirchbergQuasidiagonalAnswer_of_tikuisisWhiteWinter`
proves the question on the class of L317, and
`manuscriptSentence_uctFaithfulTrace_stablyFinite_and_quasidiagonal_of_tikuisisWhiteWinter`
records both halves of "answers this": every algebra of the class satisfies the
hypothesis of the question and its conclusion.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedTWW

noncomputable section

universe u

/-! ## The unconditional part -/

/-- **Quasidiagonal ⇒ stably finite** (L315--316, implicit in the question). -/
theorem manuscriptSentence_quasidiagonalImpliesStablyFinite
    (A : Type u) [CStarAlgebra A] (h : IsQuasidiagonalCStarAlgebra A) :
    IsStablyFiniteCStarAlgebra A :=
  isStablyFiniteCStarAlgebra_of_isQuasidiagonalCStarAlgebra h

/-- **Quasidiagonal ⇒ MF.** -/
theorem manuscriptSentence_quasidiagonalImpliesMF
    (A : Type u) [CStarAlgebra A] (h : IsQuasidiagonalCStarAlgebra A) :
    IsMFAlgebra A :=
  isMFAlgebra_of_isQuasidiagonalCStarAlgebra h

/-- **The printed question is the converse** (L315--316). Because quasidiagonal
algebras are stably finite, the question holds exactly when stable finiteness
and quasidiagonality coincide for separable nuclear C⋆-algebras. -/
theorem manuscriptSentence_blackadarKirchbergQuestion_iff :
    BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        CStarExactness.IsNuclearCStarAlgebra A →
          (IsStablyFiniteCStarAlgebra A ↔ IsQuasidiagonalCStarAlgebra A) := by
  constructor
  · intro hq A _ hsep hnuc
    exact ⟨hq A hsep hnuc, isStablyFiniteCStarAlgebra_of_isQuasidiagonalCStarAlgebra⟩
  · intro h A _ hsep hnuc hsf
    exact (h A hsep hnuc).mp hsf

/-- **A faithful trace forces stable finiteness** (L317). -/
theorem manuscriptSentence_faithfulTraceStablyFinite
    (A : Type u) [CStarAlgebra A] (τ : FaithfulTracialState A) :
    IsStablyFiniteCStarAlgebra A :=
  GroupApproximation.NinetyNineProblems.isStablyFiniteCStarAlgebra_of_faithfulTracialState τ

/-- **A faithful quasidiagonal trace gives a quasidiagonal algebra** (the step
from L279--281 to "answers this" at L318). -/
theorem manuscriptSentence_quasidiagonal_of_faithful_quasidiagonalTrace
    (A : Type u) [CStarAlgebra A] (hsep : TopologicalSpace.SeparableSpace A)
    (τ : FaithfulTracialState A)
    (hqd : Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)) :
    IsQuasidiagonalCStarAlgebra A :=
  isQuasidiagonalCStarAlgebra_of_faithful_quasidiagonalTrace hsep τ hqd

/-! ## The answer, from the recalled theorem -/

/-- **"The theorem of Tikuisis, White, and Winter recalled above answers
this"** (L316--318). On separable nuclear algebras that satisfy the UCT and have
a faithful trace, stably finite algebras are quasidiagonal. -/
theorem manuscriptSentence_blackadarKirchbergQuasidiagonalAnswer_of_tikuisisWhiteWinter
    {T : KK.KasparovTheory.{u}} (htww : TikuisisWhiteWinterStatement T) :
    BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace T := by
  intro S hnuc _ huct hτ
  obtain ⟨τ⟩ := hτ
  exact isQuasidiagonalCStarAlgebra_of_faithful_quasidiagonalTrace
    inferInstance τ (htww S hnuc huct τ)

/-- **Both halves of "answers this".** Every separable nuclear UCT algebra with
a faithful trace satisfies the question's hypothesis (it is stably finite) and
its conclusion (it is quasidiagonal). So the class of L317 is a genuine
subclass of the question, and the question is answered there. -/
theorem manuscriptSentence_uctFaithfulTrace_stablyFinite_and_quasidiagonal_of_tikuisisWhiteWinter
    {T : KK.KasparovTheory.{u}} (htww : TikuisisWhiteWinterStatement T)
    (S : KK.SepCStarAlgebra.{u}) (hnuc : CStarExactness.IsNuclearCStarAlgebra S)
    (huct : T.SatisfiesUCT S) (hτ : Nonempty (FaithfulTracialState S)) :
    IsStablyFiniteCStarAlgebra S ∧ IsQuasidiagonalCStarAlgebra S := by
  obtain ⟨τ⟩ := hτ
  exact ⟨GroupApproximation.NinetyNineProblems.isStablyFiniteCStarAlgebra_of_faithfulTracialState τ,
    isQuasidiagonalCStarAlgebra_of_faithful_quasidiagonalTrace
      inferInstance τ (htww S hnuc huct τ)⟩

end

end RelatedTWW
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.RelatedTWW

#audit_axioms manuscriptSentence_quasidiagonalImpliesStablyFinite
#audit_axioms manuscriptSentence_quasidiagonalImpliesMF
#audit_axioms manuscriptSentence_blackadarKirchbergQuestion_iff
#audit_axioms manuscriptSentence_faithfulTraceStablyFinite
#audit_axioms manuscriptSentence_quasidiagonal_of_faithful_quasidiagonalTrace
#audit_axioms manuscriptSentence_blackadarKirchbergQuasidiagonalAnswer_of_tikuisisWhiteWinter
#audit_axioms manuscriptSentence_uctFaithfulTrace_stablyFinite_and_quasidiagonal_of_tikuisisWhiteWinter
