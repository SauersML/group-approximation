import GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.AFClosed
import GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.CommQDTraceAnswer
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.PointEvalQD
import GroupApproximation.Meta.AxiomGuard

/-!
# The commutative ∪ AF subclass answer, fully unconditional (lane `nm-tww-35`)

Census row `82cac0c03a39`, `non_mf_groups_exist.tex` L315--318:

> It also asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal; for algebras that satisfy the universal coefficient theorem
> and have a faithful trace, the theorem of Tikuisis, White, and Winter recalled
> above answers this~\cite{TWW}.

**SUBCLASS ONLY.** `Answer.lean` (lane `nm-tww-05`) answers the question on separable
algebras that are commutative or have a unital AF presentation, over the two interfaces
`hcomm : CommutativeQuasidiagonalTraceStatement` and `haf : AFQuasidiagonalTraceStatement`.
`CommQDTraceAnswer.lean` (lane `nm-tww-33`) removed `hcomm`. This module removes `haf` with
`afClosed_afQuasidiagonalTraceStatement_holds` (`AFClosed.lean`), so no hypothesis beyond
the printed ones remains. It does not formalize the printed sentence, which ranges over all
UCT algebras with a faithful trace; that needs the full TWW theorem at Kasparov's `KK`.

## Endpoints

* `afClosed_isQuasidiagonalTrace_commutativeOrAF`: faithful traces on the subclass are
  quasidiagonal.
* `afClosed_isQuasidiagonalTrace_commutativeOrAF_tracialState`: the same for every tracial
  state.
* `afClosed_blackadarKirchberg_commutativeOrAF`: the Blackadar--Kirchberg answer on the
  subclass, at every Kasparov theory `T`.
* `afClosed_tikuisisWhiteWinterCommutativeOrAF`: the TWW statement restricted to the
  subclass, at every `T`.
* `afClosed_af_stablyFinite_quasidiagonal`,
  `afClosed_commutativeOrAF_stablyFinite_quasidiagonal`: an algebra of the subclass with a
  faithful trace is stably finite and quasidiagonal.

(The commutative-only endpoint of `Answer.lean` is already unconditional as
`commQDTrace_commutative_stablyFinite_uct_quasidiagonal` in `CommQDTraceAnswer.lean`.)

## Import discipline

Imports `AFClosed`, `CommQDTraceAnswer` (hence `CommQDTrace`, `Answer`, `Interfaces`) and
`CommutativeQD/PointEvalQD`. None of these imports an `AFClosed*` module.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace SubclassAnswer

/-- **Faithful traces on commutative or AF algebras are quasidiagonal**, unconditionally. -/
theorem afClosed_isQuasidiagonalTrace_commutativeOrAF
    (S : KK.SepCStarAlgebra.{0})
    (hS : S.IsCommutative ∨ Nonempty (MultimatrixAFPresentation S))
    (τ : FaithfulTracialState S) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a) :=
  commQDTrace_isQuasidiagonalTrace_commutativeOrAF_of_AF
    afClosed_afQuasidiagonalTraceStatement_holds S hS τ

/-- **Every tracial state on a commutative or AF algebra is quasidiagonal**,
unconditionally. Faithfulness is not assumed. -/
theorem afClosed_isQuasidiagonalTrace_commutativeOrAF_tracialState
    (S : KK.SepCStarAlgebra.{0})
    (hS : S.IsCommutative ∨ Nonempty (MultimatrixAFPresentation S))
    (τ : TracialState S) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a) := by
  rcases hS with hc | ⟨P⟩
  · exact CommutativeQD.pointEval_isQuasidiagonalTrace_of_commutative_tracialState hc τ
  · exact afClosed_isQuasidiagonalTrace_of_multimatrixAFPresentation_tracialState P τ

/-- **The Blackadar--Kirchberg question on the commutative ∪ AF subclass**, at every
Kasparov theory `T` (L315--318, SUBCLASS ONLY), unconditionally. A separable algebra that
is commutative or AF, stably finite, satisfies the UCT, and has a faithful tracial state is
quasidiagonal. -/
theorem afClosed_blackadarKirchberg_commutativeOrAF
    (T : KK.KasparovTheory.{0}) (S : KK.SepCStarAlgebra.{0})
    (hS : S.IsCommutative ∨ Nonempty (MultimatrixAFPresentation S)) :
    IsStablyFiniteCStarAlgebra S → T.SatisfiesUCT S →
      Nonempty (FaithfulTracialState S) →
        RelatedTWW.IsQuasidiagonalCStarAlgebra S :=
  commQDTrace_blackadarKirchberg_commutativeOrAF_of_AF
    afClosed_afQuasidiagonalTraceStatement_holds T S hS

/-- **The TWW statement restricted to commutative ∪ AF algebras holds at every Kasparov
theory `T`**, unconditionally. -/
theorem afClosed_tikuisisWhiteWinterCommutativeOrAF (T : KK.KasparovTheory.{0}) :
    TikuisisWhiteWinterCommutativeOrAFStatement T :=
  commQDTrace_tikuisisWhiteWinterCommutativeOrAF_of_AF
    afClosed_afQuasidiagonalTraceStatement_holds T

/-- **An AF algebra with a faithful trace is stably finite and quasidiagonal**
(SUBCLASS ONLY), unconditionally. -/
theorem afClosed_af_stablyFinite_quasidiagonal (S : KK.SepCStarAlgebra.{0})
    (P : MultimatrixAFPresentation S) (τ : FaithfulTracialState S) :
    IsStablyFiniteCStarAlgebra S ∧ RelatedTWW.IsQuasidiagonalCStarAlgebra S :=
  ⟨RelatedTWW.manuscriptSentence_faithfulTraceStablyFinite S τ,
    RelatedTWW.manuscriptSentence_quasidiagonal_of_faithful_quasidiagonalTrace
      S inferInstance τ (afClosed_afQuasidiagonalTraceStatement_holds S P τ)⟩

/-- **A commutative or AF algebra with a faithful trace is stably finite and
quasidiagonal** (SUBCLASS ONLY), unconditionally. -/
theorem afClosed_commutativeOrAF_stablyFinite_quasidiagonal (S : KK.SepCStarAlgebra.{0})
    (hS : S.IsCommutative ∨ Nonempty (MultimatrixAFPresentation S))
    (τ : FaithfulTracialState S) :
    IsStablyFiniteCStarAlgebra S ∧ RelatedTWW.IsQuasidiagonalCStarAlgebra S :=
  ⟨RelatedTWW.manuscriptSentence_faithfulTraceStablyFinite S τ,
    RelatedTWW.manuscriptSentence_quasidiagonal_of_faithful_quasidiagonalTrace
      S inferInstance τ (afClosed_isQuasidiagonalTrace_commutativeOrAF S hS τ)⟩

end SubclassAnswer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_isQuasidiagonalTrace_commutativeOrAF
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_isQuasidiagonalTrace_commutativeOrAF_tracialState
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_blackadarKirchberg_commutativeOrAF
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_tikuisisWhiteWinterCommutativeOrAF
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_af_stablyFinite_quasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_commutativeOrAF_stablyFinite_quasidiagonal
