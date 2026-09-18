import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.RankThree
import GroupApproximation.Meta.AxiomGuard

/-!
# The padded rank-three kernel dies (lane sk-leavitt-04, endpoint)

Carto `sk-leavitt` lane 04, last step: `stab N₃ ≤ ⁅stab St_3, stab N₃⁆ = 1`, where `N₃ = K₂(3, L)`.

* `K2_three_le_commutator_of_superperfect` (sibling `KernelCommutator.RankThree`, proved) gives
  `N₃ ≤ ⁅St_3, N₃⁆` from superperfectness of `Lˣ`.
* `Subgroup.map_commutator` pushes this through `stab`, so
  `stab N₃ ≤ ⁅stab St_3, stab N₃⁆ ≤ ⁅St_4, stab N₃⁆`.
* If `stab N₃` is central in `St_4(L)`, then `⁅St_4, stab N₃⁆ = ⊥`.

## Remaining interface

Padded centrality is lane sk-leavitt-03 (`stab_K2_le_center`, Khanh Lemma 5.6), which runs in
parallel and is not on disk.  `BinaryLeavittPaddedCentralThreeStatement` is its special case
`n = 3`, `R = L`.  That is strictly weaker than lane 03's theorem, which covers every ring and
every `n ≥ 3`.  It is true: Khanh Lemma 5.6 for any ring, and trivially here, since
`K₂(3, L) = ⊥` (Khanh Thm 5.4).  Once lane 03 lands, `stab_K2_le_center (n := 3) le_rfl`
discharges it directly.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Interface of lane sk-leavitt-03 at `n = 3`, `R = L`** (Khanh Lemma 5.6): the padding
`stab : St_3(L) → St_4(L)` carries `K₂(3, L)` into the center of `St_4(L)`.

*Why it is true.*  If `projection k = 1`, then `stab k` commutes with every `x_{i,last}(a)` and
`x_{last,j}(b)`, and these generate `St_4`, since `x_{ij}(a) = ⁅x_{i,last}(a), x_{last,j}(1)⁆`.
Not proved in this lane. -/
def BinaryLeavittPaddedCentralThreeStatement : Prop :=
  (K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).map
      (stab 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) ≤
    Subgroup.center (St (3 + 1) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittPaddedCentralThreeStatement

/-- **Lane 04 endpoint.**  From padded centrality (lane 03 at rank three) and superperfectness of
`Lˣ`, the padding `stab : St_3(L) → St_4(L)` kills `K₂(3, L)`. -/
theorem stabKernelThreeTrivial_of_paddedCentral_of_superperfect
    (hc : BinaryLeavittPaddedCentralThreeStatement)
    (hs : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement := by
  have hle := K2_three_le_commutator_of_superperfect hs
  have hbot : ⁅(⊤ : Subgroup
        (St (3 + 1) (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))),
      (K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).map
        (stab 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_center_iff.mp (hc hh) g).symm
  have hmap := Subgroup.map_mono
    (f := stab 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) hle
  rw [Subgroup.map_commutator] at hmap
  have htop := Subgroup.commutator_mono
    (le_top : (⊤ : Subgroup
        (St 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))).map
      (stab 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) ≤ ⊤)
    (le_refl ((K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).map
      (stab 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))))
  rw [hbot] at htop
  exact le_bot_iff.mp (hmap.trans htop)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stabKernelThreeTrivial_of_paddedCentral_of_superperfect

/-- **Lane 04, interface form.**  Padded centrality at rank three discharges lane 15's
interface `EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement`. -/
theorem stabKernelThreeTrivialOfSuperperfect_of_paddedCentral
    (hc : BinaryLeavittPaddedCentralThreeStatement) :
    EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement :=
  stabKernelThreeTrivial_of_paddedCentral_of_superperfect hc

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stabKernelThreeTrivialOfSuperperfect_of_paddedCentral

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
