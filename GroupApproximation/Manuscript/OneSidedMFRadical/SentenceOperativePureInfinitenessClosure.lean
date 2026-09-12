import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity

/-!
# The operative pure-infiniteness input

The manuscript does not use a topological or module-theoretic definition of
pure infiniteness in its simplicity proof.  Census row 227 says exactly which
algebraic fragment is used there: every nonzero coefficient sandwiches to the
unit.  This file gives that role a paper-facing name while keeping the
definition transparent and entirely internal.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

/-- The precise algebraic form of pure infiniteness consumed by the printed
simplicity argument, with no additional literature content hidden in it. -/
def OperativePureInfinitenessInput (S : Type*) [Ring S] : Prop :=
  HasSingleSandwichDivision S

/-- **Sentence 227.**  The binary Leavitt coefficient ring has the exact
operative pure-infiniteness input used by the ensuing root-extraction proof. -/
theorem manuscriptSentence227_operativePureInfiniteness :
    OperativePureInfinitenessInput R :=
  coefficientRing_hasSingleSandwichDivision

/-- The paper-facing predicate unfolds to the displayed two-sided sandwich
statement, so the named sentence contains no opaque strengthening. -/
theorem operativePureInfinitenessInput_iff (S : Type*) [Ring S] :
    OperativePureInfinitenessInput S ↔
      ∀ x : S, x ≠ 0 → ∃ a b : S, a * x * b = 1 :=
  Iff.rfl

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
