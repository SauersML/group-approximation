import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownWired.Stable
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.RankThree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.BinaryThree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.PaddedKill.RankThree
import GroupApproximation.Meta.AxiomGuard

/-!
# Superperfect units from the rank-three coinvariant kernel (lane sk-leavitt-30)

Here `L = L_{𝔽₂}(1,2)` and `N₃ = K₂(3, L) = ker (St_3(L) → E_3(L))`.  Every SK endpoint now
needs only `EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement` (`hsp`).

## Grep result (no unconditional input on disk)

None of these has an unconditional proof in the repo:
* `hS` / `hT` (`StableReduction.StableKTwo`);
* `hU` (`UsedStatement.LeavittK2UsedStatement`);
* `Full.LVHopf.HopfMultiplierTrivial Lˣ`, `Full.LVSuperperfect.IsSuperperfect Lˣ`;
* `SkRows.HopfFiveTerm.HopfMultiplierTrivial (E₃ L)`.

The stable routes need two inputs, the Hopf and Brown routes one.  So this lane isolates one
input on the Brown route.

## Isolated statement

`BinaryLeavittKernelThreeCoinvariantStatement : N₃ ≤ ⁅St_3(L), N₃⁆`, i.e. the
`St_3(L)`-coinvariants of `N₃` vanish.

Reduction `binaryLeavittUnitsSuperperfect_of_kernelThreeCoinvariant`, built only from theorems
already on disk:
1. Padded centrality (`binaryLeavittPaddedCentralThreeStatement_holds`) together with
   `Subgroup.map_commutator` gives `stab N₃ ≤ ⁅St_4, stab N₃⁆ = ⊥`.
2. Brown criterion: `EdgeTriangleLift.rankFourInjective_of_stabKernelThreeTrivial_holds`.
3. `EdgeTriangleLift.binaryLeavittRankFourInjective_iff_unitsSuperperfect`.

## Why strictly smaller in proof content

* `hsp` quantifies over every type `E`, every group structure and every central extension.
  The isolated statement is a single subgroup inclusion inside the one countable group
  `St_3(L)`.  It concerns only the universal extension `St_3(L) ↠ E_3(L)`.
* It is the elementary Hopf-formula shape (`R ∩ [F,F] ≤ [F,R]` for the Steinberg presentation of
  `E_3(L) ≅ Lˣ`).  So Lyndon/Brown word computations inside `St_3(L)` can prove it directly,
  without constructing arbitrary extensions.
* It already follows from the on-disk ring-generic five-term step
  (`binaryLeavittKernelThreeCoinvariant_of_hopf`).

## LOUD equivalence warning

*Modulo theorems already on disk*, the statement is equivalent to `hsp`:
`binaryLeavittKernelThreeCoinvariant_iff_unitsSuperperfect` is proved below.  It is therefore
NOT logically weaker once the corpus is imported; it is smaller only in proof content.  Its
depth is still `H₂(Lˣ) = 0` (Khanh Thm 2.2), which is research-level.

## Truth check

TRUE.  Khanh Thm 2.2 (`Lˣ` acyclic) gives `H₂(Lˣ) = 0`, hence `hsp`, hence the statement
(`binaryLeavittKernelThreeCoinvariant_of_unitsSuperperfect`).  It also holds trivially from
`K₂(3, L) = ⊥` (Khanh Thm 5.4).  No false statement was found on disk.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Isolated input (lane sk-leavitt-30).**  The `St_3(L)`-coinvariants of `K₂(3, L)` vanish:
`K₂(3, L) ≤ ⁅St_3(L), K₂(3, L)⁆` for `L = L_{𝔽₂}(1,2)`.

*Justification.*  It is a single subgroup inclusion in the countable group `St_3(L)`, with no
quantification over extensions.  So it is strictly smaller in proof content than
`EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`, and it implies that statement
(`binaryLeavittUnitsSuperperfect_of_kernelThreeCoinvariant`).  It is TRUE by Khanh Thm 2.2 via
`K2_three_le_commutator_of_superperfect`, and also by Khanh Thm 5.4 (`K₂(3, L) = ⊥`).

LOUD: modulo on-disk theorems it is equivalent to superperfectness of `Lˣ`
(`binaryLeavittKernelThreeCoinvariant_iff_unitsSuperperfect`). -/
def BinaryLeavittKernelThreeCoinvariantStatement : Prop :=
  K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ≤
    ⁅(⊤ : Subgroup (St 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))),
      K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))⁆

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittKernelThreeCoinvariantStatement

/-- **Coinvariant kernel kills the padding.**  `K₂(3, L) ≤ ⁅St_3, K₂(3, L)⁆` gives
`stab K₂(3, L) = ⊥` in `St_4(L)`.  Proof: `Subgroup.map_commutator` and the proved padded
centrality `binaryLeavittPaddedCentralThreeStatement_holds` (Khanh Lemma 5.6). -/
theorem binaryLeavittStabKernelThreeTrivial_of_kernelThreeCoinvariant
    (hle : BinaryLeavittKernelThreeCoinvariantStatement) :
    EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement := by
  have hc := binaryLeavittPaddedCentralThreeStatement_holds
  have hle' : K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ≤
      ⁅(⊤ : Subgroup (St 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))),
        K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))⁆ := hle
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
    (f := stab 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) hle'
  rw [Subgroup.map_commutator] at hmap
  have htop := Subgroup.commutator_mono
    (le_top : (⊤ : Subgroup
        (St 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))).map
      (stab 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) ≤ ⊤)
    (le_refl ((K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).map
      (stab 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))))
  rw [hbot] at htop
  exact le_bot_iff.mp (hmap.trans htop)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittStabKernelThreeTrivial_of_kernelThreeCoinvariant

/-- **Lane sk-leavitt-30 endpoint (`_of_` reduction).**  The rank-three coinvariant kernel
statement implies that `Lˣ` is superperfect.  Route: padded kill
(`binaryLeavittStabKernelThreeTrivial_of_kernelThreeCoinvariant`), then the Brown criterion
(`EdgeTriangleLift.rankFourInjective_of_stabKernelThreeTrivial_holds`), then
`EdgeTriangleLift.binaryLeavittRankFourInjective_iff_unitsSuperperfect`. -/
theorem binaryLeavittUnitsSuperperfect_of_kernelThreeCoinvariant
    (hle : BinaryLeavittKernelThreeCoinvariantStatement) :
    EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.binaryLeavittRankFourInjective_iff_unitsSuperperfect.mp
    (GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.rankFourInjective_of_stabKernelThreeTrivial_holds
      (binaryLeavittStabKernelThreeTrivial_of_kernelThreeCoinvariant hle))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittUnitsSuperperfect_of_kernelThreeCoinvariant

/-- **Truth check (converse).**  Superperfectness of `Lˣ` gives the coinvariant statement
(`K2_three_le_commutator_of_superperfect`).  So Khanh Thm 2.2 (`Lˣ` acyclic) makes the isolated
statement TRUE. -/
theorem binaryLeavittKernelThreeCoinvariant_of_unitsSuperperfect
    (hs : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    BinaryLeavittKernelThreeCoinvariantStatement :=
  K2_three_le_commutator_of_superperfect hs

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittKernelThreeCoinvariant_of_unitsSuperperfect

/-- **LOUD: equivalence modulo the corpus.**  The isolated statement is equivalent to
superperfectness of `Lˣ` once the on-disk theorems are available.  It is smaller only in proof
content, not in logical strength. -/
theorem binaryLeavittKernelThreeCoinvariant_iff_unitsSuperperfect :
    BinaryLeavittKernelThreeCoinvariantStatement ↔
      EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  ⟨binaryLeavittUnitsSuperperfect_of_kernelThreeCoinvariant,
    binaryLeavittKernelThreeCoinvariant_of_unitsSuperperfect⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittKernelThreeCoinvariant_iff_unitsSuperperfect

/-- **Hopf-formula route into the isolated statement.**  A trivial presentation-free Hopf
multiplier of the one group `E_3(L)` gives the coinvariant statement.  This uses the proved
ring-generic five-term step `SkRows.PaddedKill.K2_three_le_commutator_of_hopf`. -/
theorem binaryLeavittKernelThreeCoinvariant_of_hopf
    (h : GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm.HopfMultiplierTrivial
      (GroupApproximation.elementaryGroup (Fin 3)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))) :
    BinaryLeavittKernelThreeCoinvariantStatement :=
  GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill.K2_three_le_commutator_of_hopf
    (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittKernelThreeCoinvariant_of_hopf

/-- **Hopf-formula route to superperfect units.**  `H₂(E_3(L)) = 0` (presentation-free form)
implies `EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`. -/
theorem binaryLeavittUnitsSuperperfect_of_hopfElementaryThree
    (h : GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm.HopfMultiplierTrivial
      (GroupApproximation.elementaryGroup (Fin 3)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))) :
    EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  binaryLeavittUnitsSuperperfect_of_kernelThreeCoinvariant
    (binaryLeavittKernelThreeCoinvariant_of_hopf h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittUnitsSuperperfect_of_hopfElementaryThree

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
