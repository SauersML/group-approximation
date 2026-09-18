import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.Extension
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.Main
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown bridge VI: lane 14's Brown extension, unconditional (lane sk-leavitt-20)

Route: `FrameCone.binaryLeavittFrameConeFour` (the rank-four frame cone) plugged into
`brownExtension_of_frameConeFour` gives `Criterion.BrownExtensionStatement`.  This file is kept
separate from `BrownBridge.Extension` so that the reduction does not import the frame-cone proof.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge

/-- **Brown's extension property for `GL₄(L₂(𝔽₂))`**, unconditional. -/
theorem brownExtension : Criterion.BrownExtensionStatement :=
  brownExtension_of_frameConeFour FrameCone.binaryLeavittFrameConeFour

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.brownExtension

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge
