import GroupApproximation.Manuscript.NonMF.Full.NMWire2.Root
import GroupApproximation.Manuscript.NonMF.Full.NMWire.Census
import GroupApproximation.Manuscript.NonMF.Full.NMWire.CopyCell
import GroupApproximation.Manuscript.NonMF.Full.GL06h4.NearestShortPocket
import GroupApproximation.Meta.AxiomGuard

/-!
# Census of the residual leaves below the NM roots after the corrected pocket discharge

The corrected enclosed pocket `GL03BPinch.InnerPocketEnclosedTwoArcCorrected` is proved as
`GL03BPinch.innerPocketEnclosedTwoArcCorrected` (`GL03BPinch/Endpoint`).  This module removes it
from the census of `NMWire.Census`, at universes `0, 0, 0`.

* `nmWire2_CopyLeaves` is `NMWire.nmWire_CopyLeaves` without its `hencl` conjunct, and
  `nmWire2_copyLeaves_iff` proves the two equivalent.
* `nmWire2_LeafCensus` and `nmWire2_MinimalLeaves` do the same for `NMWire.nmWire_LeafCensus`
  and `NMWire.nmWire_MinimalLeaves`.
* `nmWire2_CopyResiduals` replaces Route A's short pocket and nearest cell pocket by the weaker
  all-cells refutation.  `nmWire2_ResidualCensus` and `nmWire2_MinimalResiduals` are the
  resulting census and minimal set.  Each closes both roots.

## Residual Props for `GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints`

This is `nmWire2_ResidualCensus` read as a list.  It needs one residual 10 alternative and one
binder 5 alternative.

Residual 10 (`PocketOuterPinchStepSectionStatement`), one of:

`GroupApproximation.Full.GL06f.RoseRegionMoveSubArcStatement`
`GroupApproximation.Full.GL03D.KeptSubwalkStatement`
`GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement`

or else, via `NMWire2.Lobe`, the name below.  It is split only to keep the line length:

`GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.`
`roseJunctionCore_LobeRemovalStatement`

Binder 5 (`OsinMultipleEdgePocketRegionCopyBelowSectionStatement`), Route A:

`GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`

or Route B, which is the first of these together with one of the other three:

`GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseUncutStatement`
`GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.AllCellsShortLoopStatement`
`GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.`
`CellPocketInnerTwoArcLongStatement`
`GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillOutsideStatement`

Route A has more inputs than the one above.  `GL06h4.gl06h4Nearest_shortPocketStatement`,
`GL06h4.NearestCellPocketStatement`, `GL06h3.ShortBoundaryRefutedBelowSectionStatement`,
`GL06h3.NearestCellCutSectionStatement` and `GL06h5.gl06h5_descentPocketStatement` each imply
it (`NMWire2.Copy`), so it is the one listed.

The draft route `GL06g.proof_of_innerPocketEnclosed` would have derived the all-cells refutation
from the corrected pocket.  It is not used: it still has an unresolved gap
(`ALLCELLS_REFUTATION_PENDING`).

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire2

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- The binder 5 alternatives of `NMWire.nmWire_CopyLeaves` with the proved corrected enclosed
pocket removed. -/
def nmWire2_CopyLeaves : Prop :=
  (GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{0, 0, 0} ∨
      GroupApproximation.Full.GL06h4.NearestCellPocketStatement.{0, 0, 0}) ∨
    (GreendlingerLeaf.Piece06.CellRoseUncutStatement.{0, 0, 0} ∧
      (GreendlingerLeaf.P07LakeExclusion.AllCellsShortLoopStatement.{0, 0, 0} ∨
        GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{0, 0, 0} ∨
        GreendlingerLeaf.P07LakeExclusion.LakeFillOutsideStatement.{0, 0, 0}))

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_CopyLeaves

/-- `nmWire2_CopyLeaves` is equivalent to `NMWire.nmWire_CopyLeaves`, because the corrected
enclosed pocket is proved. -/
theorem nmWire2_copyLeaves_iff : nmWire2_CopyLeaves ↔ NMWire.nmWire_CopyLeaves := by
  constructor
  · intro h
    rcases h with hA | hB
    · exact Or.inl
        (And.intro GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected.{0, 0, 0}
          hA)
    · exact Or.inr hB
  · intro h
    rcases h with ⟨_hencl, hA⟩ | hB
    · exact Or.inl hA
    · exact Or.inr hB

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_copyLeaves_iff

/-- **The leaf census after the discharge**: a residual 10 alternative and a binder 5
alternative of `nmWire2_CopyLeaves`. -/
def nmWire2_LeafCensus : Prop :=
  NMWire.nmWire_StepLeaves ∧ nmWire2_CopyLeaves

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_LeafCensus

/-- `nmWire2_LeafCensus` is equivalent to `NMWire.nmWire_LeafCensus`. -/
theorem nmWire2_leafCensus_iff : nmWire2_LeafCensus ↔ NMWire.nmWire_LeafCensus := by
  constructor
  · intro h
    obtain ⟨hstep, hcopy⟩ := h
    exact And.intro hstep (nmWire2_copyLeaves_iff.mp hcopy)
  · intro h
    obtain ⟨hstep, hcopy⟩ := h
    exact And.intro hstep (nmWire2_copyLeaves_iff.mpr hcopy)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_leafCensus_iff

/-- **The minimal leaf set after the discharge**: the kept-walk core and the short nearest
pocket. -/
def nmWire2_MinimalLeaves : Prop :=
  GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0} ∧
    GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{0, 0, 0}

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_MinimalLeaves

/-- `nmWire2_MinimalLeaves` is equivalent to `NMWire.nmWire_MinimalLeaves`. -/
theorem nmWire2_minimalLeaves_iff : nmWire2_MinimalLeaves ↔ NMWire.nmWire_MinimalLeaves := by
  constructor
  · intro h
    obtain ⟨hcore, hshort⟩ := h
    exact And.intro hcore
      (And.intro GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected.{0, 0, 0}
        hshort)
  · intro h
    obtain ⟨hcore, _hencl, hshort⟩ := h
    exact And.intro hcore hshort

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_minimalLeaves_iff
