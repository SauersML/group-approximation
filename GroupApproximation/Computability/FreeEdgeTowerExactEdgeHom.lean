import GroupApproximation.Computability.FreeEdgeTowerExactEdgeData

/-! # The old-group homomorphism for one exact HNN edge -/

namespace GroupApproximation
namespace FreeEdgeTowerExactIteration

open HNNExtension
open PresentationCodes FreeEdgeTowerCode FreeEdgeTowerSemantics

noncomputable section

namespace EdgeEquivalence

variable {c : PresentationCode} {edges : List (Raw × Raw)}

/-- The old presented group maps to the group presented after adjoining one
exact HNN edge. -/
noncomputable def oldHom (E : EdgeEquivalence c edges) :
    Carrier c →* Carrier (edgeCode c edges) :=
  (edgeCodeEquivOfSubgroupEquiv c edges E.equiv E.generator).symm.toMonoidHom.comp
    (HNNExtension.of : Carrier c →*
      HNNPresentation.Ext (codeRels c) (sourceWord c edges)
        (targetWord c edges) E.equiv)

end EdgeEquivalence

end

end FreeEdgeTowerExactIteration
end GroupApproximation
