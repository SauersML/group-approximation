import GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.Bridge
import GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# `AFQuasidiagonalTraceStatement` holds (lane `nm-tww-35`)

`Interfaces.lean` (lane `nm-tww-05`) records the interface

> every faithful tracial state on a C⋆-algebra with a unital AF presentation is
> quasidiagonal

as `AFQuasidiagonalTraceStatement`. This module proves it, and every AF endpoint of
`AFQD/` that takes the rational-amplification interface
`AFQD.MultimatrixTraceAmplificationStatement` as a hypothesis, unconditionally.

## Route

1. `AFQD.afQuasidiagonalTraceStatement_of_multimatrixTraceAmplification`
   (`AFQD/Bridge.lean`, lane `nm-tww-04`) reduces the interface to
   `AFQD.MultimatrixTraceAmplificationStatement`.
2. `MultimatrixTrace.multimatrixTraceAmplificationStatement`
   (`MultimatrixTrace/Statement.lean`, lane `nm-tww-03`) proves that statement outright:
   floor-rounded rational weights and an amplified block representation.

## Import discipline

This module imports `AFQD/Bridge.lean` and `MultimatrixTrace/Statement.lean`. Neither of
them, nor anything they import, imports an `AFClosed*` module, so there is no cycle.

## Truth check

A tracial state on `⊕ᵢ M_{kᵢ}(ℂ)` is `∑ᵢ tᵢ · tr_{kᵢ}` with `t` a probability vector; rational
approximations of `t` give unital block amplifications into `M_N(ℂ)` whose normalized
traces approximate it uniformly. Along an AF presentation these stage maps extend (Arveson,
finite-dimensional case, proved in the corpus) to ucp maps on `A`, which are asymptotically
multiplicative and trace-preserving on the dense union. The statement is true; there is no
remaining gap.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace SubclassAnswer

open scoped Matrix.Norms.L2Operator

noncomputable section

attribute [local instance] AFQD.matrixBlockCStarAlgebra AFQD.multimatrixCStarAlgebra

/-- **Every faithful tracial state on a C⋆-algebra with a unital AF presentation is
quasidiagonal.** This is `AFQuasidiagonalTraceStatement`, unconditionally. -/
theorem afClosed_afQuasidiagonalTraceStatement_holds : AFQuasidiagonalTraceStatement :=
  AFQD.afQuasidiagonalTraceStatement_of_multimatrixTraceAmplification
    MultimatrixTrace.multimatrixTraceAmplificationStatement

/-- The unbundled form over `MultimatrixAFPresentation`, faithful traces. -/
theorem afClosed_isQuasidiagonalTrace_of_multimatrixAFPresentation {A : Type}
    [CStarAlgebra A] (P : MultimatrixAFPresentation A) (τ : FaithfulTracialState A) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  afClosed_afQuasidiagonalTraceStatement_holds A P τ

/-- **AF algebras: every tracial state is quasidiagonal**, unconditionally. This is
`AFQD.isQuasidiagonalTrace_of_afPresentation_of_multimatrixTraceAmplification` with its
interface discharged. Faithfulness is not assumed. -/
theorem afClosed_isQuasidiagonalTrace_of_afPresentation {A : Type} [CStarAlgebra A]
    (P : AFQD.AFPresentation A) (τ : TracialState A) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  AFQD.isQuasidiagonalTrace_of_afPresentation_of_multimatrixTraceAmplification
    MultimatrixTrace.multimatrixTraceAmplificationStatement P τ

/-- The same over `MultimatrixAFPresentation`, for every (not necessarily faithful)
tracial state. -/
theorem afClosed_isQuasidiagonalTrace_of_multimatrixAFPresentation_tracialState {A : Type}
    [CStarAlgebra A] (P : MultimatrixAFPresentation A) (τ : TracialState A) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  afClosed_isQuasidiagonalTrace_of_afPresentation (AFQD.AFPresentation.ofMultimatrix P) τ

/-- **One stage of the matrix model of an AF algebra**, unconditionally. This is
`AFQD.exists_stage` with its interface discharged. -/
theorem afClosed_exists_stage {A : Type} [CStarAlgebra A] (P : AFQD.AFPresentation A)
    (τ : TracialState A) (n : ℕ) :
    ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ Quasidiagonal.IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ b c : AFQD.Multimatrix (P.blocks n) (P.sizes n),
        φ (P.embed n b * P.embed n c) = φ (P.embed n b) * φ (P.embed n c)) ∧
      ∀ b : AFQD.Multimatrix (P.blocks n) (P.sizes n),
        ‖τ (P.embed n b) - normTrace Y (φ (P.embed n b))‖ ≤
          1 / ((n : ℝ) + 2) * ‖P.embed n b‖ :=
  AFQD.exists_stage MultimatrixTrace.multimatrixTraceAmplificationStatement P τ n

end

end SubclassAnswer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_afQuasidiagonalTraceStatement_holds
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_isQuasidiagonalTrace_of_multimatrixAFPresentation
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_isQuasidiagonalTrace_of_afPresentation
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_isQuasidiagonalTrace_of_multimatrixAFPresentation_tracialState
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_exists_stage
