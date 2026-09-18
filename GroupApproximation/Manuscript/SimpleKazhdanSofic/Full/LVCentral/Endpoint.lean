import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.Padded
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Central

/-!
# Padded centrality in the foreign `LeavittK2` vocabulary

`simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`), leaf T1b.ii of the `K₂(4, L) = ⊥`
tree (Khanh, arXiv:2609.08428, Lemma 5.2; Lemma 5.6 in the foreign `LeavittK2` code).

This file restates `LVCentral.map_ker_projection_le_center` in the vocabulary of
`BooneHigman.SteinbergBasic`, where `St n R`, `K2n n R` and `stab n R` are definitionally
`SteinbergGroup (Fin n) R`, `projection.ker` and `castSuccStab n R`. It also discharges the
interface `LeavittK2.BinaryLeavittPaddedCentralThreeStatement`, which is the hypothesis `hc` of
`LeavittK2.stabKernelThreeTrivial_of_paddedCentral_of_superperfect`.
-/

namespace GroupApproximation
namespace Full
namespace LVCentral

/-- **Khanh, Lemma 5.2** (`simple_kazhdan_sofic_group.tex` l.733-735), foreign vocabulary: for
every ring `R` and every `m`, `stab(K₂(m, R))` is central in `St_{m+1}(R)`. -/
theorem map_stab_K2n_le_center (m : ℕ) (R : Type*) [Ring R] :
    (BooneHigman.SteinbergBasic.K2n m R).map (BooneHigman.SteinbergBasic.stab m R) ≤
      Subgroup.center (BooneHigman.SteinbergBasic.St (m + 1) R) :=
  map_ker_projection_le_center (m := m) (B := R)

/-- **Leaf `hc` (T1b.ii)** of the LVAssembly skeleton (`simple_kazhdan_sofic_group.tex`
l.733-735): the stabilization `St_3(L) → St_4(L)` carries `K₂(3, L)` into the centre of `St_4(L)`,
where `L` is the binary Leavitt algebra over `ZMod 2`. -/
theorem binaryLeavittPaddedCentralThree :
    Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittPaddedCentralThreeStatement :=
  map_stab_K2n_le_center 3 (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))

end LVCentral
end Full
end GroupApproximation
