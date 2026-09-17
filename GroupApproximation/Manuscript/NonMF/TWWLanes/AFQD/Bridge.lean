import GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.Model
import GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.Interfaces
import GroupApproximation.Meta.AxiomGuard

/-!
# AF algebras: bridge to the subclass-answer interface of lane `nm-tww-05`

Lane `nm-tww-05` (`SubclassAnswer/Interfaces.lean`) states the faithful-trace case of
this lane as `SubclassAnswer.AFQuasidiagonalTraceStatement`, over its own structure
`SubclassAnswer.MultimatrixAFPresentation`.

That structure has the same six fields as `AFPresentation`, and both define
`Multimatrix` by the same `abbrev` body. So the conversion copies the fields one by
one. The Statement then follows from
`isQuasidiagonalTrace_of_afPresentation_of_multimatrixTraceAmplification`:
forget faithfulness (`FaithfulTracialState.toTracialState`) and apply it.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace AFQD

noncomputable section

attribute [local instance] matrixBlockCStarAlgebra multimatrixCStarAlgebra

/-- The presentation of lane `nm-tww-05`, read as an `AFPresentation`. -/
def AFPresentation.ofMultimatrix {A : Type} [CStarAlgebra A]
    (P : SubclassAnswer.MultimatrixAFPresentation A) : AFPresentation A where
  blocks := P.blocks
  sizes := P.sizes
  embed := P.embed
  injective := P.injective
  range_mono := P.range_mono
  dense := P.dense

/-- **Lane `nm-tww-05`'s AF interface**, from the rational-amplification interface of
lane `nm-tww-03`. -/
theorem afQuasidiagonalTraceStatement_of_multimatrixTraceAmplification
    (h : MultimatrixTraceAmplificationStatement) :
    SubclassAnswer.AFQuasidiagonalTraceStatement := by
  intro A _ P τ
  exact isQuasidiagonalTrace_of_afPresentation_of_multimatrixTraceAmplification h
    (AFPresentation.ofMultimatrix P) τ.toTracialState

end

end AFQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.AFPresentation.ofMultimatrix
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.afQuasidiagonalTraceStatement_of_multimatrixTraceAmplification
