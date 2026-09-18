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

Route A can also start from `GL06h4.gl06h4Nearest_shortPocketStatement`,
`GL06h4.NearestCellPocketStatement`, `GL06h3.ShortBoundaryRefutedBelowSectionStatement`,
`GL06h3.NearestCellCutSectionStatement` or `GL06h5.gl06h5_descentPocketStatement`
(`NMWire2.Copy`).  Each of these implies the all-cells refutation, so only that one is listed.

`GL06g/Endpoint` does not remove this residual.  `GL06g.proof_of_innerPocketEnclosed` and
`GL06g.proof_of_allCells` take the all-cells refutation as the explicit hypothesis `hall`
(`GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`), and `proof_of_allCells` supplies the
corrected pocket from the proved `GL03BPinch.innerPocketEnclosedTwoArcCorrected`.  So Route A's
binder 5 residual is still exactly the all-cells refutation above.

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

/-- **The zero-parameter torsion-free endpoints from the leaf census after the discharge.** -/
theorem nmWire2_torsionFreeEndpoints_of_leafCensus (h : nmWire2_LeafCensus) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  NMWire.nmWire_torsionFreeEndpoints_of_leafCensus (nmWire2_leafCensus_iff.mp h)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_leafCensus

/-- **The zero-parameter torsion-free endpoints from the minimal leaf set after the
discharge.** -/
theorem nmWire2_torsionFreeEndpoints_of_minimalLeaves (h : nmWire2_MinimalLeaves) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  NMWire.nmWire_torsionFreeEndpoints_of_minimalLeaves (nmWire2_minimalLeaves_iff.mp h)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_minimalLeaves

/-- **The residual binder 5 alternatives.**  Route A is the all-cells refutation alone.  Route B
is the uncut rose statement (Piece06) together with a P07 leaf. -/
def nmWire2_CopyResiduals : Prop :=
  GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0} ∨
    (GreendlingerLeaf.Piece06.CellRoseUncutStatement.{0, 0, 0} ∧
      (GreendlingerLeaf.P07LakeExclusion.AllCellsShortLoopStatement.{0, 0, 0} ∨
        GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{0, 0, 0} ∨
        GreendlingerLeaf.P07LakeExclusion.LakeFillOutsideStatement.{0, 0, 0}))

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_CopyResiduals

/-- Every binder 5 alternative of `nmWire2_CopyLeaves` gives a residual binder 5 alternative.
The short nearest pocket and the nearest cell pocket both imply the all-cells refutation
(`GL06h4`). -/
theorem nmWire2_copyResiduals_of_copyLeaves (h : nmWire2_CopyLeaves) : nmWire2_CopyResiduals := by
  rcases h with (hshort | hnear) | hB
  · exact Or.inl (GroupApproximation.Full.GL06h4.gl06h4Nearest_allCellsShort_of_shortPocket hshort)
  · exact Or.inl (GroupApproximation.Full.GL06h4.gl06h4Nearest_allCellsShort_of_shortPocket
      (GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocket_of_nearestCellPocket hnear))
  · exact Or.inr hB

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_copyResiduals_of_copyLeaves

/-- **Binder 5 from any residual binder 5 alternative.** -/
theorem nmWire2_copy_of_copyResiduals (h : nmWire2_CopyResiduals) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{0, 0, 0} := by
  rcases h with hall | ⟨h06, h07⟩
  · exact nmWire2_copy_of_allCells hall
  · exact NMWire.nmWire_copy_of_cellRoseUncut_proper h06 (NMWire.nmWire_proper_of_p07Leaf h07)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_copy_of_copyResiduals

/-- **The residual census**: a residual 10 alternative and a residual binder 5 alternative. -/
def nmWire2_ResidualCensus : Prop :=
  NMWire.nmWire_StepLeaves ∧ nmWire2_CopyResiduals

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_ResidualCensus

/-- The leaf census gives the residual census. -/
theorem nmWire2_residualCensus_of_leafCensus (h : nmWire2_LeafCensus) :
    nmWire2_ResidualCensus := by
  obtain ⟨hstep, hcopy⟩ := h
  exact And.intro hstep (nmWire2_copyResiduals_of_copyLeaves hcopy)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_residualCensus_of_leafCensus

/-- **Osin's Lemma 4.4 at least-area diagrams, at universes `0, 0, 0`, from the residual
census.** -/
theorem nmWire2_greendlinger_of_residualCensus (h : nmWire2_ResidualCensus) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} := by
  obtain ⟨hstep, hcopy⟩ := h
  exact NMWire.nmWire_greendlinger_of_copy_step (nmWire2_copy_of_copyResiduals hcopy)
    (NMWire.nmWire_step_of_stepLeaves hstep)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_greendlinger_of_residualCensus

/-- **The zero-parameter torsion-free endpoints from the residual census.**  This is the top NM
endpoint after the discharge. -/
theorem nmWire2_torsionFreeEndpoints_of_residualCensus (h : nmWire2_ResidualCensus) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_of_greendlinger
    (nmWire2_greendlinger_of_residualCensus h)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_residualCensus

/-- **The minimal residual set**: the kept-walk core and the all-cells refutation. -/
def nmWire2_MinimalResiduals : Prop :=
  GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0} ∧
    GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0}

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_MinimalResiduals

/-- The minimal residual set is an instance of the residual census. -/
theorem nmWire2_residualCensus_of_minimalResiduals (h : nmWire2_MinimalResiduals) :
    nmWire2_ResidualCensus := by
  obtain ⟨hcore, hall⟩ := h
  exact And.intro (Or.inr (Or.inr hcore)) (Or.inl hall)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_residualCensus_of_minimalResiduals

/-- The minimal leaf set after the discharge gives the minimal residual set. -/
theorem nmWire2_minimalResiduals_of_minimalLeaves (h : nmWire2_MinimalLeaves) :
    nmWire2_MinimalResiduals := by
  obtain ⟨hcore, hshort⟩ := h
  exact And.intro hcore
    (GroupApproximation.Full.GL06h4.gl06h4Nearest_allCellsShort_of_shortPocket hshort)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_minimalResiduals_of_minimalLeaves

/-- **The zero-parameter torsion-free endpoints from the minimal residual set.** -/
theorem nmWire2_torsionFreeEndpoints_of_minimalResiduals (h : nmWire2_MinimalResiduals) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  nmWire2_torsionFreeEndpoints_of_residualCensus (nmWire2_residualCensus_of_minimalResiduals h)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_minimalResiduals

end GroupApproximation.Full.NMWire2
