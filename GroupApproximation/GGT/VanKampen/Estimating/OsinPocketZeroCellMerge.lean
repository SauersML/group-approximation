import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMergeRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionRotate
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixCutMerge
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerEmptyTwoGon
import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapseMerged
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.Meta.AxiomGuard

/-!
# The zero-cell pocket merge

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ'_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."  The same merge
kills a multiple edge whose pocket keeps no relator cell (Lemma 9.7(b)).  Two selected regions
`a ≠ b` and the pocket between them form one pocket region `P` with no relator cell.  This file
collapses `P` to one face and reads that face as one contiguity region: the input of
`GloballyDistinguishedSectionFamily.false_of_collapse_singleton` with `absorbed = {a, b}`.

* `Embedded.boundaryStep_of_walk`: a boundary walk between boundary darts is a boundary step,
  the converse of `Embedded.boundaryStep_to_walk` (`FaceSetBoundaryReclosed`).
* `PocketRegion.innerBoundary`: the embedded boundary on the union.  Its cycle is the pocket
  cycle, when the pocket has no relator cell and its cycle follows the boundary.  The disc
  condition of `P.inner` alone does not give the chain of boundary steps.
* `PocketRegion.toInnerGRegion`: the inner G-region, with the value of
  `Surgery.InnerGRegion.ofPocketRegion` (no shelling).
* `Surgery.InnerGRegion.mergedGeometry`: if the boundary cycle of a region, started at any dart,
  is a reversed cell arc, a side, a target arc and a side, the merged face `{R.merged}` is a
  contiguity region with the same target, arc lengths and target start.
* `GloballyDistinguishedSectionFamily.false_of_zeroCellPocket`: the assembly, with weight
  hypothesis `a.weight + b.weight ≤ |source| + |target|`.
* `GloballyDistinguishedSectionFamily.false_of_emptyTwoGon` and `emptyTwoGonFollowsInput`: the
  empty two-gon of `Φ'_M` (C6, `EmptyTwoGonInput`), when the pocket cycle follows the boundary.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Embedded

variable {Delta : DiscDiagram.{u, w, v} W} {faces : Finset Delta.toCombMap.Face}

/-- An internal vertex step is an elementary boundary move (the converse of
`internalBoundaryMove_to_skip`). -/
theorem skip_to_internalBoundaryMove {d e : Delta.toCombMap.Dart}
    (h : Surgery.MapCollapse.InternalDart Delta.toCombMap faces d ∧
      Delta.toCombMap.sigma d = e) :
    InternalBoundaryMove Delta faces d e := by
  obtain ⟨⟨hd, hda⟩, rfl⟩ := h
  refine ⟨hd, hda, ?_⟩
  change Delta.toCombMap.sigma d =
    Delta.toCombMap.sigma (Delta.toCombMap.alpha (Delta.toCombMap.alpha d))
  rw [Delta.toCombMap.alpha_involutive d]

/-- A boundary walk is a run of elementary boundary moves. -/
theorem boundaryWalk_to_moves {d e : Delta.toCombMap.Dart}
    (h : Surgery.MapCollapse.BoundaryWalk Delta.toCombMap faces d e) :
    Relation.ReflTransGen (InternalBoundaryMove Delta faces) (Delta.toCombMap.facePerm d) e := by
  unfold Surgery.MapCollapse.BoundaryWalk at h
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih (skip_to_internalBoundaryMove hstep)

/-- **Two boundary darts joined by a boundary walk form a boundary step.** -/
theorem boundaryStep_of_walk {d e : Delta.toCombMap.Dart}
    (hd : Surgery.MapCollapse.IsBoundaryDart Delta.toCombMap faces d)
    (he : Surgery.MapCollapse.IsBoundaryDart Delta.toCombMap faces e)
    (h : Surgery.MapCollapse.BoundaryWalk Delta.toCombMap faces d e) :
    BoundaryStep Delta faces d e :=
  ⟨hd, he, boundaryWalk_to_moves h⟩

end Embedded

namespace PocketRegion

variable {Delta : DiscDiagram.{u, w, v} W}

/-- Consecutive darts of the pocket cycle, cyclically, are joined by a boundary walk when the
cycle follows the boundary. -/
theorem boundaryWalk_getElem (P : PocketRegion Delta) (hwalk : P.inner.FollowsBoundary)
    (i : ℕ) (hi : i < P.inner.cycle.length) :
    Surgery.MapCollapse.BoundaryWalk Delta.toCombMap P.faces P.inner.cycle[i]
      (P.inner.cycle[(i + 1) % P.inner.cycle.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))) := by
  classical
  have h := hwalk ⟨P.inner.cycle[i], (P.inner.cycle_mem_iff _).mp (List.getElem_mem hi)⟩
  rw [Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val,
    List.next_getElem _ P.inner.cycle_nodup i hi] at h
  exact h

/-- **The embedded boundary on the union.**  A pocket with no relator cell whose cycle follows
the boundary has an embedded boundary with the same cycle. -/
def innerBoundary (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) (hwalk : P.inner.FollowsBoundary) :
    Embedded.FaceSetBoundary Delta P.faces where
  faces_nonempty :=
    ⟨_, ((P.inner.cycle_mem_iff _).mp (List.head_mem P.inner.cycle_nonempty)).1⟩
  all_gCells face hface := by
    have hne : face ≠ Delta.outerFace := fun h => P.outerFace_not_mem (h ▸ hface)
    refine ⟨hne, (Delta.inner_face face hne).resolve_left ?_⟩
    rintro ⟨C, hC, rfl⟩
    exact hcells C hC hface
  cycle := P.inner.cycle
  cycle_nonempty := P.inner.cycle_nonempty
  cycle_nodup := P.inner.cycle_nodup
  cycle_mem_iff := P.inner.cycle_mem_iff
  cycle_chain := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have h := P.boundaryWalk_getElem hwalk i (by omega)
    simp only [Nat.mod_eq_of_lt hi] at h
    exact Embedded.boundaryStep_of_walk
      ((P.inner.cycle_mem_iff _).mp (List.getElem_mem (by omega)))
      ((P.inner.cycle_mem_iff _).mp (List.getElem_mem hi)) h
  cycle_closes := by
    have hlen : 0 < P.inner.cycle.length := List.length_pos_of_ne_nil P.inner.cycle_nonempty
    have hsucc : P.inner.cycle.length - 1 + 1 = P.inner.cycle.length := by omega
    have h := P.boundaryWalk_getElem hwalk (P.inner.cycle.length - 1) (by omega)
    simp only [hsucc, Nat.mod_self] at h
    rw [List.getLast_eq_getElem, List.head_eq_getElem]
    exact Embedded.boundaryStep_of_walk
      ((P.inner.cycle_mem_iff _).mp (List.getElem_mem (by omega)))
      ((P.inner.cycle_mem_iff _).mp (List.getElem_mem hlen)) h

theorem innerBoundary_cycle (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) (hwalk : P.inner.FollowsBoundary) :
    (P.innerBoundary hcells hwalk).cycle = P.inner.cycle :=
  rfl

/-- **The inner G-region of a pocket with no relator cell whose cycle follows the boundary.**
Its boundary value comes from `Surgery.InnerGRegion.ofPocketRegion`, not from a shelling. -/
def toInnerGRegion (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) (hwalk : P.inner.FollowsBoundary) :
    Surgery.InnerGRegion Delta :=
  Surgery.InnerGRegion.ofPocketRegion P hcells (P.innerBoundary hcells hwalk)
    (List.IsRotated.refl _)

theorem toInnerGRegion_faces (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) (hwalk : P.inner.FollowsBoundary) :
    (P.toInnerGRegion hcells hwalk).faces = P.faces :=
  rfl

theorem toInnerGRegion_boundary_cycle (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) (hwalk : P.inner.FollowsBoundary) :
    (P.toInnerGRegion hcells hwalk).boundary.cycle = P.inner.cycle :=
  rfl

end PocketRegion

namespace Surgery.InnerGRegion

variable {Delta : DiscDiagram.{u, w, v} W} (R : InnerGRegion Delta)

/-- No dart of the boundary cycle of a region is internal. -/
theorem cycle_not_internal {d : Delta.toCombMap.Dart} (hd : d ∈ R.boundary.cycle) :
    ¬ MapCollapse.InternalDart Delta.toCombMap R.faces d :=
  R.not_internal_of_faceOf_alpha_not_mem ((R.boundary.cycle_mem_iff d).mp hd).2

/-- The sides of a decomposition of the rotated boundary cycle have no internal dart. -/
theorem sides_not_internal {k : ℕ} {l₁ l₂ l₃ l₄ : List Delta.toCombMap.Dart}
    (hdecomp : R.boundary.cycle.rotate k = l₁ ++ l₂ ++ l₃ ++ l₄) :
    (∀ d ∈ l₂, ¬ MapCollapse.InternalDart Delta.toCombMap R.faces d) ∧
      ∀ d ∈ l₄, ¬ MapCollapse.InternalDart Delta.toCombMap R.faces d := by
  have hmem : ∀ d ∈ l₁ ++ l₂ ++ l₃ ++ l₄,
      ¬ MapCollapse.InternalDart Delta.toCombMap R.faces d := by
    intro d hd
    rw [← hdecomp] at hd
    exact R.cycle_not_internal (List.mem_rotate.mp hd)
  exact ⟨fun d hd => hmem d (by simp [hd]), fun d hd => hmem d (by simp [hd])⟩

/-- **The merged face lists the boundary cycle of the region.** -/
theorem faceBoundary_merged_darts_eq_map_keep :
    (R.diagram.faceBoundary R.merged).darts = R.boundary.cycle.map R.keep := by
  apply List.map_injective_iff.mpr R.val_injective
  rw [R.faceBoundary_merged_map_val, R.map_keep_val fun d hd => R.cycle_not_internal hd]

/-- **A decomposition of the rotated boundary cycle decomposes the merged face.** -/
theorem faceBoundary_merged_rotate {k : ℕ} {source : Fin Delta.rCellCount}
    {target : Option (Fin Delta.rCellCount)} (sourceArc : CyclicArc (cellDarts Delta source))
    (targetArc : CyclicArc (targetDarts Delta target))
    {rightSide leftSide : List Delta.toCombMap.Dart}
    (hdecomp : R.boundary.cycle.rotate k =
      sourceArc.reverseDarts ++ rightSide ++ targetBoundaryDarts Delta target targetArc ++
        leftSide) :
    (R.diagram.faceBoundary R.merged).darts.rotate k =
      (sourceArc.mapTo R.keep (R.cellDarts_eq source)).reverseDarts ++ rightSide.map R.keep ++
        targetBoundaryDarts R.diagram (target.map R.cellMap.indexEquiv)
          (targetArc.mapTo R.keep (R.targetDarts_eq target)) ++ leftSide.map R.keep := by
  rw [R.faceBoundary_merged_darts_eq_map_keep, ← List.map_rotate, hdecomp,
    R.reverseDarts_mapTo (fun d hd => R.cellDarts_not_internal source hd) sourceArc
      (R.cellDarts_eq source),
    R.targetBoundaryDarts_map target targetArc]
  simp only [List.map_append]

section Merged

variable {D : RelGenSet G Lambda} {eps : ℕ} {k : ℕ} {source : Fin Delta.rCellCount}
  {target : Option (Fin Delta.rCellCount)} (sourceArc : CyclicArc (cellDarts Delta source))
  (targetArc : CyclicArc (targetDarts Delta target))
  {rightSide leftSide : List Delta.toCombMap.Dart}
  (hdecomp : R.boundary.cycle.rotate k =
    sourceArc.reverseDarts ++ rightSide ++ targetBoundaryDarts Delta target targetArc ++ leftSide)
  (hright : rightSide.length ≤ eps) (hleft : leftSide.length ≤ eps)
  (hrightNorm : WordMetric.wordNorm D.alphabet.carrier
    (RelLetter.listVal (dartWord Delta rightSide)) ≤ eps)
  (hleftNorm : WordMetric.wordNorm D.alphabet.carrier
    (RelLetter.listVal (dartWord Delta leftSide)) ≤ eps)

/-- **The merged face as one contiguity region.**  If the boundary cycle of `R`, started at some
dart, is a reversed arc of a relator cell, a side, an arc of the target and a side, the merged
face is a contiguity region with the transported arcs and sides. -/
noncomputable def mergedGeometry :
    ContiguityGeometry D eps R.diagram ({R.merged} : Finset R.diagram.toCombMap.Face) :=
  ContiguityGeometry.ofSingletonFace R.merged R.merged_ne_outer R.merged_value
    R.merged_noInternalFaceDart k (R.cellMap.indexEquiv source)
    (target.map R.cellMap.indexEquiv) (sourceArc.mapTo R.keep (R.cellDarts_eq source))
    (targetArc.mapTo R.keep (R.targetDarts_eq target)) (rightSide.map R.keep)
    (leftSide.map R.keep) (R.faceBoundary_merged_rotate sourceArc targetArc hdecomp)
    (by rw [List.length_map]; exact hright) (by rw [List.length_map]; exact hleft)
    (by rw [R.dartWord_map (R.sides_not_internal hdecomp).1]; exact hrightNorm)
    (by rw [R.dartWord_map (R.sides_not_internal hdecomp).2]; exact hleftNorm)

theorem mergedGeometry_target :
    (R.mergedGeometry sourceArc targetArc hdecomp hright hleft hrightNorm
      hleftNorm).target = target.map R.cellMap.indexEquiv :=
  rfl

theorem mergedGeometry_sourceArc_length :
    (R.mergedGeometry sourceArc targetArc hdecomp hright hleft hrightNorm
      hleftNorm).sourceArc.length = sourceArc.length :=
  sourceArc.mapTo_length R.keep (R.cellDarts_eq source)

theorem mergedGeometry_targetArc_length :
    (R.mergedGeometry sourceArc targetArc hdecomp hright hleft hrightNorm
      hleftNorm).targetArc.length = targetArc.length :=
  targetArc.mapTo_length R.keep (R.targetDarts_eq target)

theorem mergedGeometry_targetArc_start :
    (R.mergedGeometry sourceArc targetArc hdecomp hright hleft hrightNorm
      hleftNorm).targetArc.start.1 = targetArc.start.1 :=
  targetArc.mapTo_start R.keep (R.targetDarts_eq target)

end Merged

end Surgery.InnerGRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.skip_to_internalBoundaryMove
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.boundaryWalk_to_moves
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.boundaryStep_of_walk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.boundaryWalk_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.innerBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.innerBoundary_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.toInnerGRegion
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.toInnerGRegion_faces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.toInnerGRegion_boundary_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.cycle_not_internal
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.sides_not_internal
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.faceBoundary_merged_darts_eq_map_keep
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.faceBoundary_merged_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.mergedGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.mergedGeometry_target
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.mergedGeometry_sourceArc_length
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.mergedGeometry_targetArc_length
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.mergedGeometry_targetArc_start
