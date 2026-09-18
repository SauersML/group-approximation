import GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.Interfaces
import GroupApproximation.Manuscript.NonMF.RelatedTWW.Sentence
import GroupApproximation.Analysis.UniversalCoefficientTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# TWW lanes, subclass answer: the Blackadar--Kirchberg question on commutative ∪ AF

Lane `nm-tww-05`. Census row `82cac0c03a39`, `non_mf_groups_exist.tex` L315--318:

> It also asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal; for algebras that satisfy the universal coefficient theorem
> and have a faithful trace, the theorem of Tikuisis, White, and Winter recalled
> above answers this~\cite{TWW}.

**Subclass, not the printed sentence.** The theorems below answer the question
only for separable algebras that are commutative or have a unital AF
presentation. The printed class (all UCT algebras with a faithful trace) needs
the full TWW theorem at Kasparov's `KK`, which is not available. The row stays
`attribution`; these declarations are a genuine partial answer on a subclass.

## Route

1. `isQuasidiagonalTrace_of_commutativeOrAF`: on the subclass, every faithful
   tracial state is quasidiagonal. Case split: commutative ⇒
   `CommutativeQuasidiagonalTraceStatement` (lane `nm-tww-02`); AF ⇒
   `AFQuasidiagonalTraceStatement` (lane `nm-tww-04`).
2. `manuscriptSentence_blackadarKirchbergAnswer_commutativeOrAF_of_subclassTraces`:
   Brown's argument, `RelatedTWW.manuscriptSentence_quasidiagonal_of_faithful_quasidiagonalTrace`,
   turns a faithful quasidiagonal trace into a quasidiagonal algebra. This holds at
   every Kasparov theory `T`; the UCT and stable finiteness hypotheses are not
   used.
3. `tikuisisWhiteWinterCommutativeOrAF_of_subclassTraces`: the TWW statement
   restricted to the subclass, at every `T`. It is also a consequence of the full
   `RelatedTWW.TikuisisWhiteWinterStatement T`
   (`tikuisisWhiteWinterCommutativeOrAF_of_tikuisisWhiteWinter`).
4. `manuscriptSentence_commutative_stablyFinite_uct_quasidiagonal_of_subclassTraces`:
   a commutative algebra with a faithful trace lies in the class of L317 at every
   `T` (stably finite, satisfies the UCT) and is quasidiagonal.

## Remaining gap

The two upstream Statements (lanes `nm-tww-02`, `nm-tww-04`), which were not on
disk when this lane was authored. Each is the faithful-trace case of the
upstream lane's endpoint, so it is strictly weaker than that endpoint, and it is
true (see `SubclassAnswer.Interfaces`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace SubclassAnswer

noncomputable section

/-! ## Traces on the subclass -/

/-- **Faithful traces on commutative or AF algebras are quasidiagonal**, from the
two upstream interfaces. -/
theorem isQuasidiagonalTrace_of_commutativeOrAF
    (hcomm : CommutativeQuasidiagonalTraceStatement)
    (haf : AFQuasidiagonalTraceStatement)
    (S : KK.SepCStarAlgebra.{0})
    (hS : S.IsCommutative ∨ Nonempty (MultimatrixAFPresentation S))
    (τ : FaithfulTracialState S) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a) := by
  rcases hS with hc | ⟨P⟩
  · exact hcomm S inferInstance hc τ
  · exact haf S P τ

/-! ## The restricted answer -/

/-- **The Blackadar--Kirchberg question on the commutative ∪ AF subclass**, at
every Kasparov theory `T` (L315--318, SUBCLASS ONLY). A separable algebra that is
commutative or AF, stably finite, satisfies the UCT, and has a faithful tracial
state is quasidiagonal. This is not the printed sentence, which ranges over all
UCT algebras with a faithful trace. -/
theorem manuscriptSentence_blackadarKirchbergAnswer_commutativeOrAF_of_subclassTraces
    (hcomm : CommutativeQuasidiagonalTraceStatement)
    (haf : AFQuasidiagonalTraceStatement)
    (T : KK.KasparovTheory.{0}) (S : KK.SepCStarAlgebra.{0})
    (hS : S.IsCommutative ∨ Nonempty (MultimatrixAFPresentation S)) :
    IsStablyFiniteCStarAlgebra S → T.SatisfiesUCT S →
      Nonempty (FaithfulTracialState S) →
        RelatedTWW.IsQuasidiagonalCStarAlgebra S := by
  intro _ _ hτ
  obtain ⟨τ⟩ := hτ
  exact RelatedTWW.manuscriptSentence_quasidiagonal_of_faithful_quasidiagonalTrace
    S inferInstance τ (isQuasidiagonalTrace_of_commutativeOrAF hcomm haf S hS τ)

/-! ## The TWW statement restricted to the subclass -/

/-- **The Tikuisis--White--Winter statement restricted to commutative ∪ AF
algebras**, at the Kasparov theory `T`. -/
def TikuisisWhiteWinterCommutativeOrAFStatement (T : KK.KasparovTheory.{0}) : Prop :=
  ∀ S : KK.SepCStarAlgebra.{0},
    (S.IsCommutative ∨ Nonempty (MultimatrixAFPresentation S)) →
      CStarExactness.IsNuclearCStarAlgebra S → T.SatisfiesUCT S →
        ∀ τ : FaithfulTracialState S,
          Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a)

/-- **The restricted TWW statement holds at every `T`**, from the two upstream
interfaces. Unlike the full `RelatedTWW.TikuisisWhiteWinterStatement T`, it does
not depend on `T` being Kasparov's `KK`. -/
theorem tikuisisWhiteWinterCommutativeOrAF_of_subclassTraces
    (hcomm : CommutativeQuasidiagonalTraceStatement)
    (haf : AFQuasidiagonalTraceStatement)
    (T : KK.KasparovTheory.{0}) :
    TikuisisWhiteWinterCommutativeOrAFStatement T := by
  intro S hS _ _ τ
  exact isQuasidiagonalTrace_of_commutativeOrAF hcomm haf S hS τ

/-- The full TWW statement implies its restriction to the subclass. -/
theorem tikuisisWhiteWinterCommutativeOrAF_of_tikuisisWhiteWinter
    {T : KK.KasparovTheory.{0}}
    (htww : RelatedTWW.TikuisisWhiteWinterStatement T) :
    TikuisisWhiteWinterCommutativeOrAFStatement T := by
  intro S _ hnuc huct τ
  exact htww S hnuc huct τ

/-! ## Commutative algebras lie in the class of L317 -/

/-- **A commutative algebra with a faithful trace is in the class of L317 and is
quasidiagonal**, at every Kasparov theory `T` (SUBCLASS ONLY). It is stably
finite, satisfies the UCT, and is quasidiagonal. -/
theorem manuscriptSentence_commutative_stablyFinite_uct_quasidiagonal_of_subclassTraces
    (hcomm : CommutativeQuasidiagonalTraceStatement)
    (T : KK.KasparovTheory.{0}) (S : KK.SepCStarAlgebra.{0})
    (hc : S.IsCommutative) (τ : FaithfulTracialState S) :
    IsStablyFiniteCStarAlgebra S ∧ T.SatisfiesUCT S ∧
      RelatedTWW.IsQuasidiagonalCStarAlgebra S :=
  ⟨RelatedTWW.manuscriptSentence_faithfulTraceStablyFinite S τ,
    KK.KasparovTheory.satisfiesUCT_of_isCommutative (T := T) hc,
    RelatedTWW.manuscriptSentence_quasidiagonal_of_faithful_quasidiagonalTrace
      S inferInstance τ (hcomm S inferInstance hc τ)⟩

end

end SubclassAnswer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.isQuasidiagonalTrace_of_commutativeOrAF
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.manuscriptSentence_blackadarKirchbergAnswer_commutativeOrAF_of_subclassTraces
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.TikuisisWhiteWinterCommutativeOrAFStatement
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.tikuisisWhiteWinterCommutativeOrAF_of_subclassTraces
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.tikuisisWhiteWinterCommutativeOrAF_of_tikuisisWhiteWinter
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.manuscriptSentence_commutative_stablyFinite_uct_quasidiagonal_of_subclassTraces
