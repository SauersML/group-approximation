import GroupApproximation.Computability.FreeEdgeTowerSemantics

/-! # Exact semantic data for one raw HNN edge -/

namespace GroupApproximation
namespace FreeEdgeTowerExactIteration

open PresentationCodes FreeEdgeTowerCode FreeEdgeTowerSemantics

/-- An equivalence between the generated source and target subgroups, with its
value on every displayed generator. -/
structure EdgeEquivalence (c : PresentationCode)
    (edges : List (Raw × Raw)) where
  equiv : HNNPresentation.srcSub (codeRels c) (sourceWord c edges) ≃*
    HNNPresentation.tgtSub (codeRels c) (targetWord c edges)
  generator : ∀ i,
    ((equiv ⟨HNNPresentation.srcGen (codeRels c) (sourceWord c edges) i,
        HNNPresentation.srcGen_mem (codeRels c) (sourceWord c edges) i⟩ :
      HNNPresentation.tgtSub (codeRels c) (targetWord c edges)) : Carrier c) =
      HNNPresentation.tgtGen (codeRels c) (targetWord c edges) i

end FreeEdgeTowerExactIteration
end GroupApproximation
