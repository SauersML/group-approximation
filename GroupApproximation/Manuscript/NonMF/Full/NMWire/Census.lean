import GroupApproximation.Manuscript.NonMF.Full.NMWire.Root
import GroupApproximation.Meta.AxiomGuard

/-!
# Census of the live leaves below the NM roots

This module states the live leaves of the Greendlinger waist at universes `0, 0, 0`.
`nmWire_LeafCensus` is the conjunction of the residual 10 alternatives and the binder 5
alternatives.

`nmWire_MinimalLeaves` is a minimal leaf set of three statements:

* the kept-walk core;
* the corrected enclosed pocket;
* the short nearest pocket.

Either statement closes both roots.  The residual 10 alternatives are the sub-arc region move,
the kept sub-walk, or its core.  The lobe-removal alternative is in `NMWire.Lobe`.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- The residual 10 alternatives (Piece10). -/
def nmWire_StepLeaves : Prop :=
  GroupApproximation.Full.GL06f.RoseRegionMoveSubArcStatement.{0, 0, 0} ∨
    GroupApproximation.Full.GL03D.KeptSubwalkStatement.{0, 0, 0} ∨
    GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}

#audit_axioms GroupApproximation.Full.NMWire.nmWire_StepLeaves

/-- The binder 5 alternatives.  Route A is the corrected enclosed pocket together with the short
or nearest pocket (Piece07).  Route B is the uncut rose statement (Piece06) together with a P07
leaf. -/
def nmWire_CopyLeaves : Prop :=
  (GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{0, 0, 0} ∧
      (GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{0, 0, 0} ∨
        GroupApproximation.Full.GL06h4.NearestCellPocketStatement.{0, 0, 0})) ∨
    (GreendlingerLeaf.Piece06.CellRoseUncutStatement.{0, 0, 0} ∧
      (GreendlingerLeaf.P07LakeExclusion.AllCellsShortLoopStatement.{0, 0, 0} ∨
        GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{0, 0, 0} ∨
        GreendlingerLeaf.P07LakeExclusion.LakeFillOutsideStatement.{0, 0, 0}))

#audit_axioms GroupApproximation.Full.NMWire.nmWire_CopyLeaves

/-- **The leaf census**: a residual 10 alternative and a binder 5 alternative. -/
def nmWire_LeafCensus : Prop :=
  nmWire_StepLeaves ∧ nmWire_CopyLeaves

#audit_axioms GroupApproximation.Full.NMWire.nmWire_LeafCensus

/-- **The minimal leaf set**: the kept-walk core, the corrected enclosed pocket and the short
nearest pocket. -/
def nmWire_MinimalLeaves : Prop :=
  GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0} ∧
    GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{0, 0, 0} ∧
    GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{0, 0, 0}

#audit_axioms GroupApproximation.Full.NMWire.nmWire_MinimalLeaves

/-- Residual 10 from any of its alternatives. -/
theorem nmWire_step_of_stepLeaves (h : nmWire_StepLeaves) :
    PocketOuterPinchStepSectionStatement.{0, 0, 0} := by
  rcases h with hsub | hkept | hcore
  · exact nmWire_step_of_roseRegionMoveSubArc hsub
  · exact nmWire_step_of_keptSubwalk hkept
  · exact nmWire_step_of_keptSubwalkCore hcore

#audit_axioms GroupApproximation.Full.NMWire.nmWire_step_of_stepLeaves

/-- Binder 5 from any of its alternatives. -/
theorem nmWire_copy_of_copyLeaves (h : nmWire_CopyLeaves) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{0, 0, 0} := by
  rcases h with ⟨hencl, hshort | hnear⟩ | ⟨h06, h07⟩
  · exact nmWire_copy_of_corrected_shortPocket hencl hshort
  · exact nmWire_copy_of_corrected_nearestCellPocket hencl hnear
  · exact nmWire_copy_of_cellRoseUncut_proper h06 (nmWire_proper_of_p07Leaf h07)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_copy_of_copyLeaves

/-- **Osin's Lemma 4.4 at least-area diagrams, at universes `0, 0, 0`, from the census.** -/
theorem nmWire_greendlinger_of_leafCensus (h : nmWire_LeafCensus) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  nmWire_greendlinger_of_copy_step (nmWire_copy_of_copyLeaves h.2) (nmWire_step_of_stepLeaves h.1)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_greendlinger_of_leafCensus

/-- **The zero-parameter torsion-free endpoints from the census.** -/
theorem nmWire_torsionFreeEndpoints_of_leafCensus (h : nmWire_LeafCensus) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_of_greendlinger
    (nmWire_greendlinger_of_leafCensus h)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_torsionFreeEndpoints_of_leafCensus

/-- The minimal leaf set is an instance of the census. -/
theorem nmWire_leafCensus_of_minimalLeaves (h : nmWire_MinimalLeaves) : nmWire_LeafCensus :=
  ⟨Or.inr (Or.inr h.1), Or.inl ⟨h.2.1, Or.inl h.2.2⟩⟩

#audit_axioms GroupApproximation.Full.NMWire.nmWire_leafCensus_of_minimalLeaves

/-- **The zero-parameter torsion-free endpoints from the minimal leaf set.** -/
theorem nmWire_torsionFreeEndpoints_of_minimalLeaves (h : nmWire_MinimalLeaves) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  nmWire_torsionFreeEndpoints_of_leafCensus (nmWire_leafCensus_of_minimalLeaves h)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_torsionFreeEndpoints_of_minimalLeaves

end GroupApproximation.Full.NMWire
