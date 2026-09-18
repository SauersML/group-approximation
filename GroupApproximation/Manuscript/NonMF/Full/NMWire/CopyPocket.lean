import GroupApproximation.Manuscript.NonMF.Full.GL06.BinderFive
import GroupApproximation.Manuscript.NonMF.Full.GL06h4.NearestShortPocket
import GroupApproximation.Meta.AxiomGuard

/-!
# Binder 5 from the corrected enclosed pocket and the short nearest pocket

`GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted` gives binder 5 from GL06e's
refutation below the section count.  That refutation comes from two inputs through
`GL06h4.gl06h4Nearest_refutedBelow_of_corrected_of_shortPocket`.  The first is
`GL03BPinch.InnerPocketEnclosedTwoArcCorrected`.  The second is
`GL06h4.gl06h4Nearest_shortPocketStatement`, which is implied by
`GL06h4.NearestCellPocketStatement`.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **Binder 5 from the corrected enclosed pocket and the short nearest pocket** (Osin, proof of
Lemma 9.7(b); `thm:hull`). -/
theorem nmWire_copy_of_corrected_shortPocket
    (hencl : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (hshort : GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
    (GroupApproximation.Full.GL06h4.gl06h4Nearest_refutedBelow_of_corrected_of_shortPocket
      hencl hshort)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_copy_of_corrected_shortPocket

/-- **Binder 5 from the corrected enclosed pocket and the nearest cell pocket.**  The nearest
cell pocket implies the short one. -/
theorem nmWire_copy_of_corrected_nearestCellPocket
    (hencl : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (hnear : GroupApproximation.Full.GL06h4.NearestCellPocketStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  nmWire_copy_of_corrected_shortPocket hencl
    (GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocket_of_nearestCellPocket hnear)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_copy_of_corrected_nearestCellPocket

end GroupApproximation.Full.NMWire
