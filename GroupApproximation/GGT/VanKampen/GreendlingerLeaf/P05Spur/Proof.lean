import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.Rotation
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through an outer spur thickening

Target: `GroupApproximation.GGT.VanKampen.TwoGonSpurStepStatement`.

Mathematical proof.  Let `w := FaceEdgeDoubling.dart S.diagram outerFace j`, an outer boundary
dart whose reverse also lies on the outer face (`hspur`), and let `M'` be the map obtained by
inserting the new edge `{none, some none}` at the corners `w`, `b := facePerm w`.

1. The thickening carries the family (`spurTransport`): old darts enter through `embed`, old
   faces through `faceImage`, relator cells are renumbered by `cellMap.indexEquiv`, and the
   crossings of a carried region are the images of the old crossings (`crossO_regionCandidate`),
   since `alpha w` is on no target arc.
2. The thickening carries `Φ'_M` at every component (`phiTransportAt`).  An old dart is internal
   after the step iff it was internal before; `none`, `some none`, `w` and `b` are not internal.
   The collapsed face rotation agrees along `embed` except that the predecessor of `w` now goes
   to `some none`, which continues to `embed b`; `some none` is not an old dart, and `w` is not a
   crossing dart since it has the outer face on both sides.  Face-class paths are named back by
   `backDart`, and a dart on a new relator cell face is named by one on the old cell face.
3. `hasCleanTwoGon_of_transport` carries a clean two-gon along such a transport of a least-area
   diagram.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur

universe u w v

/-- **A clean two-gon through an outer spur thickening.** -/
theorem proof : TwoGonSpurStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S j hlen hspur h
  exact hasCleanTwoGon_of_transport hlea (spurTransport S j hlen hspur)
    (fun a₀ => phiTransportAt S j hlen hspur a₀) h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.proof
