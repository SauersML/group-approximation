import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketDiscMerge
import GroupApproximation.Meta.AxiomGuard

/-!
# Route A collapses the pinched two-gon pocket

A model test for the disc-region collapse of `Estimating/OsinPocketDiscMerge.lean`
(`Surgery.InnerDiscRegion.ofPocketRegion` and `Surgery.InnerDiscRegion.mergedGeometry`).
`Estimating/OsinPocketDiscEmptyTwoGon.lean` uses that collapse to prove `EmptyTwoGonInput`, the
two-gon step of the proof of Osin's Lemma 9.7(a) (arXiv:math/0411039v3).  The test runs the
collapse on the pinched pocket `pocket` of `Estimating/OsinPocketPinchedTwoGonRegion.lean`.

* The pocket holds no relator cell (`pocket_cells_avoid`), so it is a collapsible disc region
  (`discRegion`).
* The reversed complement cycle of the pocket is the reversed arc `[0, 1]` of the relator cell `Π`
  (`sourceArc_reverseDarts`), no right side, the arc `[4, 6]` of the exterior boundary
  (`targetArc_darts`), and no left side (`outer_decomp`).  This is the decomposition hypothesis of
  `EmptyTwoGonInput`, with empty sides.
* The cycle of the disc region has the same decomposition (`discRegion_decomp`).  So the merged
  face of the collapse is a contiguity region from `Π` to the exterior, with arcs of lengths 2
  and 2 (`geometry`).

The same face set has no face-set boundary (`no_faceSetBoundary`).  Its cycle does not follow the
boundary (`not_followsBoundary`) and is not a simple closed walk (`not_isSimpleClosedWalk`).  The
collapse needs neither.  So the disc region `R` and the contiguity region `H` that
`emptyTwoGonInput_holds` passes to
`GloballyDistinguishedSectionFamily.false_of_disc_collapse_singleton` exist on a pinched pocket
(`pinchedPocketDiscCollapseModel`).  The model carries no section family, so it tests only these
geometric inputs.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel

theorem face_zero_not_mem_pinchFaces : face 0 ∉ pinchFaces := fun h =>
  (Finset.mem_cons.mp h).elim (fun h1 => absurd ((face_eq_iff 0 1).mp h1) (by decide))
    (fun h2 => absurd ((face_eq_iff 0 2).mp (Finset.mem_singleton.mp h2)) (by decide))

/-- The pocket holds no relator cell. -/
theorem pocket_cells_avoid : ∀ C ∈ diagram.relatorCells, C.face ∉ pocket.faces := by
  intro C hC
  have h : C = relatorCell := List.mem_singleton.mp hC
  subst C
  exact face_zero_not_mem_pinchFaces

/-- **The pinched pocket as a collapsible disc region.** -/
noncomputable def discRegion : Surgery.InnerDiscRegion diagram :=
  Surgery.InnerDiscRegion.ofPocketRegion pocket pocket_cells_avoid

/-- The arc `[0, 1]` of the relator cell `Π`. -/
def sourceArc : Embedded.CyclicArc (Embedded.cellDarts diagram 0) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 2
  length_le := by
    rw [diagram_cellDarts]
    decide

theorem sourceArc_darts : sourceArc.darts = [0, 1] := by
  change ((Embedded.cellDarts diagram 0).drop 0 ++
    (Embedded.cellDarts diagram 0).take 0).take 2 = _
  rw [diagram_cellDarts]
  rfl

theorem sourceArc_reverseDarts : sourceArc.reverseDarts = [5, 3] := by
  change sourceArc.darts.reverse.map diagram.toCombMap.alpha = _
  rw [sourceArc_darts]
  rfl

/-- The arc `[4, 6]` of the exterior boundary. -/
def targetArc : Embedded.CyclicArc (Embedded.targetDarts diagram none) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 2
  length_le := by
    change 2 ≤ (Embedded.outerDarts diagram).length
    rw [diagram_outerDarts]
    decide

theorem targetArc_darts : targetArc.darts = [4, 6] := by
  change ((Embedded.outerDarts diagram).drop 0 ++
    (Embedded.outerDarts diagram).take 0).take 2 = _
  rw [diagram_outerDarts]
  rfl

theorem targetBoundaryDarts_targetArc :
    Embedded.targetBoundaryDarts diagram none targetArc = [4, 6] :=
  targetArc_darts

/-- **The decomposition hypothesis of `EmptyTwoGonInput`.**  The reversed complement cycle of the
pocket is the reversed source arc, no side, the target arc and no side. -/
theorem outer_decomp :
    Embedded.invDarts diagram pocket.outer.cycle =
      sourceArc.reverseDarts ++ [] ++ targetArc.darts ++ [] := by
  rw [sourceArc_reverseDarts, targetArc_darts]
  decide

/-- The cycle of the disc region has the same decomposition. -/
theorem discRegion_decomp :
    discRegion.region.cycle.rotate 0 =
      sourceArc.reverseDarts ++ [] ++ Embedded.targetBoundaryDarts diagram none targetArc ++
        [] := by
  rw [sourceArc_reverseDarts, targetBoundaryDarts_targetArc]
  decide

theorem empty_side_norm :
    WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (Embedded.dartWord diagram ([] : List diagram.toCombMap.Dart))) ≤ 0 :=
  Nat.le_of_eq (WordMetric.wordNorm_one _)

/-- **The merged face is a contiguity region from `Π` to the exterior.** -/
noncomputable def geometry :
    Embedded.ContiguityGeometry D 0 discRegion.diagram
      ({discRegion.merged} : Finset discRegion.diagram.toCombMap.Face) :=
  discRegion.mergedGeometry sourceArc targetArc discRegion_decomp (Nat.le_refl 0) (Nat.le_refl 0)
    empty_side_norm empty_side_norm

theorem geometry_target : geometry.target = none := rfl

theorem geometry_sourceArc_length : geometry.sourceArc.length = sourceArc.length :=
  discRegion.mergedGeometry_sourceArc_length sourceArc targetArc discRegion_decomp
    (Nat.le_refl 0) (Nat.le_refl 0) empty_side_norm empty_side_norm

theorem geometry_targetArc_length : geometry.targetArc.length = targetArc.length :=
  discRegion.mergedGeometry_targetArc_length sourceArc targetArc discRegion_decomp
    (Nat.le_refl 0) (Nat.le_refl 0) empty_side_norm empty_side_norm

/-- **Route A on a pinched pocket.**  The pinched two-gon map has a pocket region `P` holding no
relator cell, whose face set has no face-set boundary and whose cycle neither follows the boundary
nor is a simple closed walk.  The reversed complement cycle of `P` is a reversed arc of the relator
cell, no side, a nonempty arc of the exterior boundary, and no side.  The collapse of `P` is a
contiguity region from the relator cell to the exterior whose arcs have the same lengths. -/
def PinchedPocketDiscCollapseModel : Prop :=
  ∃ (P : PocketRegion diagram) (hcells : ∀ C ∈ diagram.relatorCells, C.face ∉ P.faces),
    IsEmpty (Embedded.FaceSetBoundary diagram P.faces) ∧
    ¬ P.inner.toBoundaryCycle.FollowsBoundary ∧
    ¬ IsSimpleClosedWalk diagram.toCombMap P.inner.cycle ∧
    ∃ (source : Embedded.CyclicArc (Embedded.cellDarts diagram 0))
      (target : Embedded.CyclicArc (Embedded.targetDarts diagram none)),
      0 < source.length ∧ 0 < target.length ∧
      Embedded.invDarts diagram P.outer.cycle =
        source.reverseDarts ++ [] ++ target.darts ++ [] ∧
      ∃ H : Embedded.ContiguityGeometry D 0
          (Surgery.InnerDiscRegion.ofPocketRegion P hcells).diagram
          ({(Surgery.InnerDiscRegion.ofPocketRegion P hcells).merged} :
            Finset (Surgery.InnerDiscRegion.ofPocketRegion P hcells).diagram.toCombMap.Face),
        H.target = none ∧ H.sourceArc.length = source.length ∧
          H.targetArc.length = target.length

theorem pinchedPocketDiscCollapseModel : PinchedPocketDiscCollapseModel :=
  ⟨pocket, pocket_cells_avoid, no_faceSetBoundary, not_followsBoundary, not_isSimpleClosedWalk,
    sourceArc, targetArc, by decide, by decide, outer_decomp, geometry, geometry_target,
    geometry_sourceArc_length, geometry_targetArc_length⟩

#audit_axioms pocket_cells_avoid
#audit_axioms geometry
#audit_closed_axioms outer_decomp
#audit_closed_axioms geometry_sourceArc_length
#audit_closed_axioms pinchedPocketDiscCollapseModel

end GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel
