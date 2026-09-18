import GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.CommQDTrace
import GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.Answer
import GroupApproximation.Meta.AxiomGuard

/-!
# The subclass answer with the commutative interface discharged (lane `nm-tww-33`)

`Answer.lean` (lane `nm-tww-05`) proves its subclass answer to the Blackadar--Kirchberg
question (`non_mf_groups_exist.tex` L315--318, SUBCLASS ONLY) from two interfaces,
`CommutativeQuasidiagonalTraceStatement` and `AFQuasidiagonalTraceStatement`.
`CommQDTrace.lean` proves the first one (`commQDTrace_holds`). This module plugs it in.

## Endpoints

* `commQDTrace_commutative_stablyFinite_uct_quasidiagonal`: unconditional. A separable
  commutative algebra with a faithful tracial state is stably finite, satisfies the UCT at
  every Kasparov theory `T`, and is quasidiagonal.
* `commQDTrace_isQuasidiagonalTrace_commutativeOrAF_of_AF`,
  `commQDTrace_blackadarKirchberg_commutativeOrAF_of_AF`,
  `commQDTrace_tikuisisWhiteWinterCommutativeOrAF_of_AF`: the remaining `Answer.lean`
  endpoints. They now depend only on `AFQuasidiagonalTraceStatement` (lane `nm-tww-04`),
  which this lane does not own.

This does not formalize the printed sentence, which ranges over all UCT algebras with a
faithful trace.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace SubclassAnswer

/-- **Commutative algebras with a faithful trace (SUBCLASS ONLY, unconditional).** A
separable commutative C⋆-algebra with a faithful tracial state is stably finite, satisfies
the UCT at the Kasparov theory `T`, and is quasidiagonal. -/
theorem commQDTrace_commutative_stablyFinite_uct_quasidiagonal
    (T : KK.KasparovTheory.{0}) (S : KK.SepCStarAlgebra.{0})
    (hc : S.IsCommutative) (τ : FaithfulTracialState S) :
    IsStablyFiniteCStarAlgebra S ∧ T.SatisfiesUCT S ∧
      RelatedTWW.IsQuasidiagonalCStarAlgebra S :=
  manuscriptSentence_commutative_stablyFinite_uct_quasidiagonal_of_subclassTraces
    commQDTrace_holds T S hc τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.commQDTrace_commutative_stablyFinite_uct_quasidiagonal

/-- Faithful traces on commutative or AF algebras are quasidiagonal, given only the AF
interface of lane `nm-tww-04`. -/
theorem commQDTrace_isQuasidiagonalTrace_commutativeOrAF_of_AF
    (haf : AFQuasidiagonalTraceStatement)
    (S : KK.SepCStarAlgebra.{0})
    (hS : S.IsCommutative ∨ Nonempty (MultimatrixAFPresentation S))
    (τ : FaithfulTracialState S) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a) :=
  isQuasidiagonalTrace_of_commutativeOrAF commQDTrace_holds haf S hS τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.commQDTrace_isQuasidiagonalTrace_commutativeOrAF_of_AF

/-- The Blackadar--Kirchberg question on the commutative ∪ AF subclass (SUBCLASS ONLY),
given only the AF interface of lane `nm-tww-04`. -/
theorem commQDTrace_blackadarKirchberg_commutativeOrAF_of_AF
    (haf : AFQuasidiagonalTraceStatement)
    (T : KK.KasparovTheory.{0}) (S : KK.SepCStarAlgebra.{0})
    (hS : S.IsCommutative ∨ Nonempty (MultimatrixAFPresentation S)) :
    IsStablyFiniteCStarAlgebra S → T.SatisfiesUCT S →
      Nonempty (FaithfulTracialState S) →
        RelatedTWW.IsQuasidiagonalCStarAlgebra S :=
  manuscriptSentence_blackadarKirchbergAnswer_commutativeOrAF_of_subclassTraces
    commQDTrace_holds haf T S hS

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.commQDTrace_blackadarKirchberg_commutativeOrAF_of_AF

/-- The TWW statement restricted to the commutative ∪ AF subclass holds at every `T`,
given only the AF interface of lane `nm-tww-04`. -/
theorem commQDTrace_tikuisisWhiteWinterCommutativeOrAF_of_AF
    (haf : AFQuasidiagonalTraceStatement) (T : KK.KasparovTheory.{0}) :
    TikuisisWhiteWinterCommutativeOrAFStatement T :=
  tikuisisWhiteWinterCommutativeOrAF_of_subclassTraces commQDTrace_holds haf T

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.commQDTrace_tikuisisWhiteWinterCommutativeOrAF_of_AF

end SubclassAnswer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
