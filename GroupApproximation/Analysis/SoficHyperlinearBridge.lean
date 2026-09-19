import GroupApproximation.Analysis.SoficHyperlinearTrace
import GroupApproximation.Analysis.TracialQuotientCStar

/-!
# The canonical trace of a sofic group is a hyperlinear trace

The bridge, assembled.  `Analysis/SoficHyperlinearTrace.lean` proved
everything except the existence of the lift; the `CStarAlgebra` instance of
`Analysis/TracialQuotientCStarIdentity.lean` lets the universal property of
the full group C-star algebra produce it, and contractivity of a
⋆-homomorphism between C-star algebras discharges the norm hypothesis.

The statement is general: **every** countable sofic group's canonical trace
on `C*(G)` is hyperlinear, in Shulman's sequential definition, along
ordinary `atTop`, with no ultrafilter anywhere in the proof.  This is the
(H) half of the trace separation; the (M) half is
`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal`, and the two sit
in the same namespace as the matched pair the manuscript prints.
-/

namespace GroupApproximation
namespace ShulmanTrace

open Filter TracialUltraproduct SoficPermutationTrace

set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 4000000

/-- The universal sentence of the bridge, as a closed proposition: the
canonical maximal trace of every countable sofic group is a hyperlinear
trace.  The audit's zero-input gate requires advertised endpoints to have an
empty outer telescope, so the quantifiers live here rather than on the
theorem. -/
def SoficCanonicalTraceIsHyperlinear : Prop :=
  ∀ (G : Type) [Group G] [Countable G], IsSofic G →
    IsHyperlinearTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)

/-- **Soficity makes the canonical trace hyperlinear.**  For a countable
sofic group `G`, the canonical trace of the full group C-star algebra is a
hyperlinear trace: a sofic approximation's permutation matrices represent
`C*(G)` in the `atTop` tracial matrix quotient, and bounded elementwise
representatives of that representation are sequential matrix models. -/
theorem canonicalMaximalTrace_isHyperlinearTrace_of_isSofic :
    SoficCanonicalTraceIsHyperlinear := by
  intro G _ _ hG
  obtain ⟨S, hpos, -, -⟩ :=
    SoficPermutationTrace.exists_soficApproximation_tendsto_normTrace hG
  haveI : ∀ n, Nonempty (S.model n) := fun n ↦
    Fintype.card_pos_iff.mp (hpos n)
  obtain ⟨π, hπ, -⟩ := maximalGroupCStar_existsUnique_lift G (soficUnitaryHom S)
  refine isHyperlinearTrace_canonicalMaximalTrace_of_soficRepresentation
    S hpos π ?_ ?_
  · intro g
    rw [hπ g]
    rfl
  · intro a
    exact NonUnitalStarAlgHom.norm_apply_le π a

end ShulmanTrace
end GroupApproximation
