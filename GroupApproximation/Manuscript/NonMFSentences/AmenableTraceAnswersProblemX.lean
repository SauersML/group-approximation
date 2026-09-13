import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemX
import GroupApproximation.Meta.AxiomGuard

/-!
# The canonical trace of `C^*_{\max}(W)` answers Brown's question and Problem X(1)

`non_mf_groups_exist.tex`, Introduction after Theorem `thm:amenable-trace` (tex 274–277):

> The trace answers the question of Brown~\cite[discussion preceding Proposition~3.5.1]{Brown} and of
> Schafhauser, Tikuisis and White~\cite[Problem~X(1)]{STW} whether every amenable trace is quasidiagonal.

The question is the universal statement `NinetyNineProblems.ProblemX1Statement`: every amenable tracial state on
a C⋆-algebra is quasidiagonal.  "The trace" is the canonical trace of `C^*_{\max}(W)` for the group `W` of
`thm:amenable-trace`.  The sentence is carried here along the printed route: take `W` from
`AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTrace`, bundle its canonical trace as the tracial state
`ShulmanTrace.canonicalMaximalTracialState W`, and read off that this amenable, not quasidiagonal trace refutes the
universal statement.

`NinetyNineProblems.not_problemX1Statement` refutes the same statement through the marked group `E`.  This module
uses the group `W` the sentence names.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace AmenableTraceAnswersProblemX

open LiteralNonMFLinearWitness CliffordWitnessLocallyRFByInt
open LocallyRFByIntAmenableTrace

/-- **tex 274–277**: the group `W` of `thm:amenable-trace`, with its canonical maximal trace bundled as a tracial
state that is amenable and not quasidiagonal, refutes "every amenable trace is quasidiagonal". -/
def PrintedAmenableTraceAnswersProblemX1 : Prop :=
  ∃ (W K : Type) (_ : Group W) (_ : Group K) (φ : Multiplicative ℤ →* MulAut K),
    Nonempty (W ≃* (K ⋊[φ] Multiplicative ℤ)) ∧
      IsLocallyResiduallyFinite K ∧
      IsSofic W ∧
      ¬ IsOperatorMF W ∧
      Quasidiagonal.IsAmenableTrace
        (fun a : MaximalGroupCStar W ↦ ShulmanTrace.canonicalMaximalTracialState W a) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar W ↦ ShulmanTrace.canonicalMaximalTracialState W a) ∧
      ¬ NinetyNineProblems.ProblemX1Statement.{1}

/-- **The trace of `thm:amenable-trace` answers Brown's question and Problem X(1) in the negative.** -/
theorem manuscriptSentence_amenableTraceAnswersProblemX1 :
    PrintedAmenableTraceAnswersProblemX1 := by
  obtain ⟨W, K, _, _, φ, he, hK, hsof, hmf, -, hamen, hnqd⟩ :=
    AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTrace
  have hamen' : Quasidiagonal.IsAmenableTrace
      (fun a : MaximalGroupCStar W ↦ ShulmanTrace.canonicalMaximalTracialState W a) := hamen
  have hnqd' : ¬ Quasidiagonal.IsQuasidiagonalTrace
      (fun a : MaximalGroupCStar W ↦ ShulmanTrace.canonicalMaximalTracialState W a) := hnqd
  exact ⟨W, K, inferInstance, inferInstance, φ, he, hK, hsof, hmf, hamen', hnqd',
    fun hX ↦ hnqd' (hX (MaximalGroupCStar W) (ShulmanTrace.canonicalMaximalTracialState W) hamen')⟩

end AmenableTraceAnswersProblemX
end NonMFSentences
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.AmenableTraceAnswersProblemX.manuscriptSentence_amenableTraceAnswersProblemX1
