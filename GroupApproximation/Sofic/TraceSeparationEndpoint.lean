import GroupApproximation.Analysis.SoficHyperlinearBridge
import GroupApproximation.Sofic.LiteralTraceConsequence

/-!
# A hyperlinear trace that is not an MF trace

The trace-class separation, at the literal group.  `E` is sofic
(`LiteralSoficAssembly.markedGroup_isSofic`), so its canonical trace on
`C*(E)` is hyperlinear by the general bridge
`ShulmanTrace.canonicalMaximalTrace_isHyperlinearTrace_of_isSofic`; and that
same trace is not an MF trace
(`LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace`).
Both trace classes are Shulman's sequential definitions, frozen in
`Analysis/ShulmanTraceClasses.lean` and `Analysis/ShulmanTraceNorms.lean`:
the same five clauses, with the three algebraic defects measured in
normalized Hilbert--Schmidt norm for the first and operator norm for the
second.

So not every hyperlinear trace is MF.  The separating trace lives on a
separable unital C-star algebra — `C*(E)` for a countable group `E` — which
is the shape in which the literature poses the question.
-/

namespace GroupApproximation
namespace LiteralTraceConsequence

open LiteralNonMFPresentation

/-- **The canonical trace of `C*(E)` is hyperlinear and is not an MF
trace.**  The hyperlinear half is soficity of `E` through the general
bridge; the MF half is the trace-level form of Theorem A. -/
theorem markedGroup_canonicalTrace_isHyperlinearTrace_not_isMFTrace :
    ShulmanTrace.IsHyperlinearTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦
        canonicalMaximalTrace MarkedGroup a) ∧
    ¬ ShulmanTrace.IsMFTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦
        canonicalMaximalTrace MarkedGroup a) :=
  ⟨ShulmanTrace.canonicalMaximalTrace_isHyperlinearTrace_of_isSofic
      MarkedGroup LiteralSoficAssembly.markedGroup_isSofic,
    markedGroup_canonicalMaximalTrace_not_isMFTrace⟩

/-- The separation packaged with the ambient facts the printed theorem
carries: `C*(E)` is separable, and its canonical trace is a hyperlinear
trace that is not an MF trace.  Unitality is intrinsic to
`MaximalGroupCStar`. -/
theorem markedGroup_separable_canonicalTrace_hyperlinear_not_isMFTrace :
    TopologicalSpace.SeparableSpace (MaximalGroupCStar MarkedGroup) ∧
    ShulmanTrace.IsHyperlinearTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦
        canonicalMaximalTrace MarkedGroup a) ∧
    ¬ ShulmanTrace.IsMFTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦
        canonicalMaximalTrace MarkedGroup a) :=
  ⟨maximalGroupCStar_separableSpace MarkedGroup,
    markedGroup_canonicalTrace_isHyperlinearTrace_not_isMFTrace.1,
    markedGroup_canonicalTrace_isHyperlinearTrace_not_isMFTrace.2⟩

end LiteralTraceConsequence

/-- The universal sentence of `lem:mftrace-group`, as a closed proposition:
for every countable group, an MF canonical trace on the full group C-star
algebra makes the group operator MF\@.  The audit's zero-input gate requires
advertised endpoints to have an empty outer telescope, so the quantifiers
live here rather than on the theorem. -/
def MFTraceGroupBridge : Prop :=
  ∀ (G : Type*) [Group G] [Countable G],
    ShulmanTrace.IsMFTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) →
    IsOperatorMF G

/-- Manuscript wrapper for `lem:mftrace-group`.  The content is
`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal`. -/
theorem manuscriptMFTraceGroupBridge : MFTraceGroupBridge :=
  fun _ _ _ h ↦ ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal h

end GroupApproximation
