import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
-- import <module of Full.LVStableK2.binaryLeavitt_stableK2Trivial>        (LVH2GL3 work order W1)
-- import <module of Full.LVStability.binaryLeavitt_k2StabInjective>   (LVH2GL3 work order W2)

/-!
# `hsp`: the unit group of `L = L_{𝔽₂}(1,2)` is superperfect (lane LVSuperperfect endpoint)

`simple_kazhdan_sofic_group.tex` l.733-735 (binder `hsp`).  UNLANDED DRAFT: waits for W1, W2.
-/

namespace GroupApproximation.Full.LVSuperperfect

theorem binaryLeavittUnitsSuperperfect :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  isSuperperfect_binaryLeavittUnits_iff.mp
    (LVH2GL3.binaryLeavittUnits_isSuperperfect_of_stable LVStableK2.binaryLeavitt_stableK2Trivial
      (fun _ hm => LVStability.binaryLeavitt_k2StabInjective hm))

end GroupApproximation.Full.LVSuperperfect
