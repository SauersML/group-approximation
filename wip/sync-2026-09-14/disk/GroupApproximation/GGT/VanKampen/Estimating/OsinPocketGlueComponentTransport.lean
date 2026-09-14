import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueComponentCarriers
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.Estimating.Partition
import GroupApproximation.Meta.AxiomGuard

/-!
# Transports of a pocket region without following cycles

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): a region of a copy of `Γ_1` to the arc `t_1`
of a cell, or to the arc `t_2` of the boundary, glues back into a region of a copy of `Δ`, with the
same contiguity degree.

`pocketCellTransport` and `pocketOuterTransport` glue the copy along a complement cycle that follows
the boundary.  At a full source arc the cycle does not follow and the glued map can split
(`OsinPocketFullArcLakeGlueModel`).  Here `Δ` is least area in place of following, and the region
has a nonempty source arc.  Take the exterior component of the glued map, planar by
`PocketGlueComponentPlanarStatement`: it is O-equivalent to `Δ` and carries every relator cell
(`PocketRegion.componentOEquivalent`).  The region is joined to its source cell, so it lies on the
component and embeds into it (`PocketRegion.componentEmbedding`).  Its image target darts read the
image arc of the cell, or lie on the image arc of the boundary.

* `PocketCellTransportEulerStatement`, `PocketOuterTransportEulerStatement`: the transports, with
  least area in place of following and a nonempty source arc.
* `pocketCellTransportEuler`, `pocketOuterTransportEuler`: both, from
  `PocketGlueComponentPlanarStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, through Osin's Lemma 9.7(b)); certifies no printed
sentence on its own.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open Embedded HullSC Surgery.MapCollapse Surgery.PocketGlue

universe u w v

/-- **Transport to a cell, without following.**  Let `X` be least area, and let the inverse
complement cycle of a pocket region of `X` contain, after `pre`, an arc of a cell `t` outside the
pocket read backwards.  A region with a nonempty source arc of an O-equivalent copy of the pocket
to that part of its boundary glues back into a region of an O-equivalent copy of `X` from a cell
to another cell, with the same contiguity degree. -/
def PocketCellTransportEulerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (P : PocketRegion X),
    X.LeastArea →
      ∀ (t : Fin X.rCellCount), (cell X t).face ∉ P.faces →
        ∀ (arc : CyclicArc (cellDarts X t)) (pre post : List X.toCombMap.Dart),
          invDarts X P.outer.cycle = pre ++ invDarts X arc.darts ++ post →
            ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram P.diagram Xi →
              ∀ a : RegionCandidate D eps Xi, a.2.target = none → a.2.sourceArc.length ≠ 0 →
                pre.length ≤ a.2.targetArc.start.1 →
                  a.2.targetArc.start.1 + a.2.targetArc.length ≤ pre.length + arc.length →
                    ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
                      (t' : Fin Y.rCellCount),
                      Nonempty (OEquivalentDiscDiagram X Y) ∧ b.2.target = some t' ∧
                        b.2.source ≠ t' ∧ b.contiguityDegree = a.contiguityDegree

/-- **Transport to the boundary, without following.**  Let `X` be least area, and let the inverse
complement cycle of a pocket region of `X` contain, after `pre`, an arc of `∂X` without
wrap-around.  A region with a nonempty source arc of an O-equivalent copy of the pocket to that
part of its boundary glues back into a region of an O-equivalent copy of `X` to `∂X` inside the
arc, with the same contiguity degree. -/
def PocketOuterTransportEulerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (P : PocketRegion X),
    X.LeastArea →
      ∀ (arc : CyclicArc (outerDarts X)), arc.start.1 + arc.length ≤ (outerDarts X).length →
        ∀ (pre post : List X.toCombMap.Dart),
          invDarts X P.outer.cycle = pre ++ arc.darts ++ post →
            ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram P.diagram Xi →
              ∀ a : RegionCandidate D eps Xi, a.2.target = none → a.2.sourceArc.length ≠ 0 →
                pre.length ≤ a.2.targetArc.start.1 →
                  a.2.targetArc.start.1 + a.2.targetArc.length ≤ pre.length + arc.length →
                    ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y),
                      Nonempty (OEquivalentDiscDiagram X Y) ∧ b.2.target = none ∧
                        arc.start.1 ≤ b.2.targetArc.start.1 ∧
                        b.2.targetArc.start.1 + b.2.targetArc.length ≤
                          arc.start.1 + arc.length ∧
                        b.contiguityDegree = a.contiguityDegree

/-- **Transport to a cell, without following** (Osin, arXiv:math/0411039v3, §9, proof of Lemma
9.7(b)), from the planarity of the components of the glued copy. -/
theorem pocketCellTransportEuler (hplan : PocketGlueComponentPlanarStatement.{u, w, v}) :
    PocketCellTransportEulerStatement.{u, w, v} := by
  intro G _ Lambda D eps W X P hlea t ht arc pre post hsplit Xi O a hnone hsrc hlo hhi
  have hplanar := hplan X P Xi O (P.glueOuterDart O)
  have hs : Xi.outerFace ∉ a.1 := fun h => (a.2.boundary.all_gCells _ h).1 rfl
  let E := P.componentEmbedding O hplanar hs (P.componentOf_of_region O hplanar hlea a.2 hsrc)
  obtain ⟨src, hsrcd⟩ := P.exists_componentCell O hplanar hlea a.2.source
  obtain ⟨j, hj⟩ := P.exists_componentLeftCell O hplanar hlea t ht
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hlo
  have hml : m + a.2.targetArc.length ≤ arc.length := by omega
  have hdec : a.2.boundary.cycle =
      a.2.sourceArc.reverseDarts ++ a.2.rightSide ++ a.2.targetArc.darts ++ a.2.leftSide :=
    a.2.boundary_decomposition.trans (by rw [targetBoundaryDarts_of_eq_none hnone a.2.targetArc])
  refine ⟨P.componentDiagram O hplanar,
    ⟨E.faceSet, E.retargetGeometry a.2 src hsrcd a.2.targetArc.darts hdec (some j)
      (P.componentCellArc O hplanar hj arc m a.2.targetArc.length hml)
      (P.componentCellArc_boundaryDarts O hplanar hlea ht hj arc hsplit a.2.targetArc m hm hml)⟩,
    j, ⟨P.componentOEquivalent O hplanar hlea⟩, rfl, ?_, ?_⟩
  · -- The source cell comes from the copy, the target cell from `X`.
    intro heq
    have hcd : (cellDarts Xi a.2.source).map (P.componentDart O hplanar) =
        (cellDarts X t).map (P.componentLeftDart O hplanar) :=
      hsrcd.symm.trans ((congrArg (cellDarts (P.componentDiagram O hplanar)) heq).trans hj)
    have hmemXi : (cell Xi a.2.source).face ∈ Xi.relatorCells.map RelatorCell.face :=
      List.mem_map_of_mem (cell_mem Xi a.2.source)
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _
      (Xi.faceBoundary (cell Xi a.2.source).face).nonempty
    have hxface : Xi.toCombMap.faceOf x = (cell Xi a.2.source).face :=
      ((Xi.faceBoundary _).mem_iff x).mp hx
    have hmem : P.componentDart O hplanar x ∈ (cellDarts X t).map (P.componentLeftDart O hplanar) := by
      rw [← hcd]
      exact List.mem_map_of_mem hx
    obtain ⟨d, hd, hdx⟩ := List.mem_map.1 hmem
    have hdface : X.toCombMap.faceOf d = (cell X t).face := ((X.faceBoundary _).mem_iff d).mp hd
    have hgo : (cell X t).face ∈ P.outside := (P.mem_outside_iff _).2 ht
    have hdout : X.toCombMap.faceOf d ∈ (P.glueSeam O).faces := by
      rw [hdface]
      exact hgo
    have hxdom := P.componentOf_glueEmbedding_of_face_mem O hplanar hlea hmemXi hxface
    have hddom := P.componentOf_leftIncl_of_face_mem O hplanar hlea
      (List.mem_map_of_mem (cell_mem X t)) hgo hdface
    have hne : Xi.toCombMap.faceOf x ≠ (P.glueSeam O).outer :=
      fun h => DiscDiagram.relFace_ne_outerFace hmemXi (hxface.symm.trans h)
    have hval := congrArg Subtype.val hdx
    rw [P.componentLeftDart_val O hplanar hddom, P.componentDart_val O hplanar hxdom,
      (P.glueSeam O).leftIncl_of_mem _ hdout, (P.glueSeam O).glueEmbedding_of_ne x hne] at hval
    exact Sum.inl_ne_inr hval
  · show ((a.2.sourceArc.mapTo (P.componentDart O hplanar) hsrcd).length : ℝ) /
        ((cell (P.componentDiagram O hplanar) src).word.length : ℝ) =
      (a.2.sourceArc.length : ℝ) / ((cell Xi a.2.source).word.length : ℝ)
    rw [CyclicArc.mapTo_length, ← CellBoundaryPartition.cellDarts_length_eq_word_length,
      ← CellBoundaryPartition.cellDarts_length_eq_word_length, hsrcd, List.length_map]

/-- **Transport to the boundary, without following** (Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b)), from the planarity of the components of the glued copy. -/
theorem pocketOuterTransportEuler (hplan : PocketGlueComponentPlanarStatement.{u, w, v}) :
    PocketOuterTransportEulerStatement.{u, w, v} := by
  intro G _ Lambda D eps W X P hlea arc hend pre post hdec Xi O a ht hsrc hpre hA
  have hplanar := hplan X P Xi O (P.glueOuterDart O)
  have hs : Xi.outerFace ∉ a.1 := fun h => (a.2.boundary.all_gCells _ h).1 rfl
  let E := P.componentEmbedding O hplanar hs (P.componentOf_of_region O hplanar hlea a.2 hsrc)
  obtain ⟨src, hsrcd⟩ := P.exists_componentCell O hplanar hlea a.2.source
  obtain ⟨B, hb1, hb2, hBd⟩ :=
    P.exists_component_outerArc_within O hplanar arc hend pre post hdec a.2.targetArc hpre hA
  have hdec' : a.2.boundary.cycle =
      a.2.sourceArc.reverseDarts ++ a.2.rightSide ++ a.2.targetArc.darts ++ a.2.leftSide :=
    a.2.boundary_decomposition.trans (by rw [targetBoundaryDarts_of_eq_none ht a.2.targetArc])
  refine ⟨P.componentDiagram O hplanar,
    ⟨E.faceSet, E.retargetGeometry a.2 src hsrcd a.2.targetArc.darts hdec' none B hBd⟩,
    ⟨P.componentOEquivalent O hplanar hlea⟩, rfl, hb1, hb2, ?_⟩
  show ((a.2.sourceArc.mapTo (P.componentDart O hplanar) hsrcd).length : ℝ) /
      ((cell (P.componentDiagram O hplanar) src).word.length : ℝ) =
    (a.2.sourceArc.length : ℝ) / ((cell Xi a.2.source).word.length : ℝ)
  rw [CyclicArc.mapTo_length, ← CellBoundaryPartition.cellDarts_length_eq_word_length,
    ← CellBoundaryPartition.cellDarts_length_eq_word_length, hsrcd, List.length_map]

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketCellTransportEulerStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketOuterTransportEulerStatement
#audit_axioms GroupApproximation.GGT.VanKampen.pocketCellTransportEuler
#audit_axioms GroupApproximation.GGT.VanKampen.pocketOuterTransportEuler
