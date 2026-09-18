import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.Residual
import GroupApproximation.Meta.AxiomGuard

/-!
# An in-order filter move from a quadrant move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-91.

Target: `P10Rose.RoseRegionMoveSubArcStatement` (equivalently `GL06f.RoseRegionMoveSubArcStatement`
and `GL03DKept.gl03dKept_KeptSubwalkCoreStatement`), through an in-order filter move
`P10RegionSubArc.subArc_FilterMove K z`.

* `p10FM_exists_filterMove`: for a pocket face set `K` under the hypotheses of the target, the
  residual `p10FM_QuadrantMoveStatement` (module `Residual`) instantiated at
  `M = X.toCombMap`, `F = K.faces`, `c = K.boundary`, `o = X.outerFace`, `s`, `k` the faces of
  `K.source` and `K.kept`, `a = K.sourceArc`, `b = K.targetArc`, `s₁ = K.firstSide`,
  `s₂ = K.secondSide` gives a quadrant colouring `z`, and `z` is an in-order filter move:
  - region constancy and independence: `p10FM_z_step`, `p10FM_z_indep` (module `Colour`);
  - the outer face and the source cell stay out, the kept cell stays in: `p10FM_not_mem_flip`,
    `p10FM_mem_flip` with `K.outerFace_not_mem`, `K.source_not_mem`, `K.kept_mem`;
  - the kept infix of `K.sourceArc⁻¹` is `t₁⁻¹` for an arc `t₁` of the source cell:
    `P10RoseLobe.roseLobeFL_exists_arc_invDarts_of_infix`;
  - the kept prefix of `K.targetArc` is an arc `t₂` inside the old window:
    `P10RoseLobe.roseLobeFL_exists_arc_of_prefix_drop` with `k = 0`;
  - the kept darts form a closed dart walk: from the residual.
  The hypotheses of the residual are those of `K`: `X.planar`, `K.ClosedWalk`, and, by
  definitional unfolding, `¬K.FirstTurns`, `P10ChordLift.AllNonFirstTurnsCrossed K`,
  `K.decomposition` (`invDarts`), `cellDarts`, `outerDarts`, and
  `RelatorCell.face_ne_outer` for `s ≠ o`.
* `p10FM_regionMoveSubArc`: the target, by `P10RegionSubArc.subArc_goal_of_filterMove`.
* `p10FM_roseStep`: the rose step, by `P10Rose.rose_of_regionMoveSubArc`.

The only open input is `p10FM_QuadrantMoveStatement`; see module `Residual` for its strength
(LOUD: not logically weaker than the target, only smaller in proof content) and its truth check.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **An in-order filter move exists** for every pocket face set under the hypotheses of
`P10Rose.RoseRegionMoveSubArcStatement`, given the quadrant move. -/
theorem p10FM_exists_filterMove (h : p10FM_QuadrantMoveStatement.{v})
    (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) (hnft : ¬ K.FirstTurns)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (hpinch : ¬Unpinched X.toCombMap K.faces)
    (hrose : P10ChordLift.AllNonFirstTurnsCrossed K) :
    ∃ z : X.toCombMap.Dart → Bool, P10RegionSubArc.subArc_FilterMove K z := by
  have hw : IsClosedDartWalk X.toCombMap K.boundary.cycle :=
    ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  obtain ⟨B, p, q, hB, ho, hs, hk, hy, hT, hT2, hwalk⟩ :=
    h X.toCombMap K.faces K.boundary X.outerFace (cell X K.source).face (cell X K.kept).face
      (X.faceBoundary (cell X K.source).face) (X.faceBoundary X.outerFace) K.sourceArc
      K.targetArc K.firstSide K.secondSide X.planar hw hpinch hnft hrose K.outerFace_not_mem
      K.source_not_mem (cell X K.source).face_ne_outer K.kept_mem hsrc htgt K.decomposition
  have hc := K.boundary.cycle_mem_iff
  have hT' : (invDarts X K.sourceArc.darts).filter
      (movePred X.toCombMap (p10FM_z X.toCombMap K.faces B p q)) <:+:
        invDarts X K.sourceArc.darts := hT
  obtain ⟨t₁, ht₁⟩ := P10RoseLobe.roseLobeFL_exists_arc_invDarts_of_infix X K.sourceArc hT'
  have hstart : K.targetArc.start.1 + 0 ≤ (outerDarts X).length := by
    have := K.targetArc.start.isLt
    omega
  have hT2' : K.targetArc.darts.filter
      (movePred X.toCombMap (p10FM_z X.toCombMap K.faces B p q)) <+:
        K.targetArc.darts.drop 0 := by
    rw [List.drop_zero]
    exact hT2
  obtain ⟨t₂, ht₂, hst, hend⟩ :=
    P10RoseLobe.roseLobeFL_exists_arc_of_prefix_drop K.targetArc hstart hT2'
  refine ⟨p10FM_z X.toCombMap K.faces B p q, ?_⟩
  unfold P10RegionSubArc.subArc_FilterMove
  exact ⟨p10FM_z_step X.toCombMap K.faces hB hc p q, p10FM_z_indep X.toCombMap K.faces hc p q,
    p10FM_not_mem_flip X.toCombMap hB hc K.outerFace_not_mem ho, hy,
    p10FM_not_mem_flip X.toCombMap hB hc K.source_not_mem hs,
    ⟨K.kept, p10FM_mem_flip X.toCombMap hB hc K.kept_mem hk⟩, ⟨t₁, ht₁⟩,
    ⟨t₂, ht₂.symm, hst, hend⟩, hwalk⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_exists_filterMove

end Pocket

/-- **The sub-arc region move from the quadrant move.** -/
theorem p10FM_regionMoveSubArc (h : p10FM_QuadrantMoveStatement.{v}) :
    P10Rose.RoseRegionMoveSubArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi _ _ K hK hnft hsrc htgt hpinch hrose
  obtain ⟨z, hz⟩ := p10FM_exists_filterMove h K hK hnft hsrc htgt hpinch hrose
  have hgoal := P10RegionSubArc.subArc_goal_of_filterMove K hsrc htgt hz
  unfold P10RegionSubArc.subArc_Goal at hgoal
  exact hgoal

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_regionMoveSubArc

/-- **The rose step from the quadrant move**, through `P10Rose.rose_of_regionMoveSubArc`. -/
theorem p10FM_roseStep (h : p10FM_QuadrantMoveStatement.{v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  P10Rose.rose_of_regionMoveSubArc (p10FM_regionMoveSubArc h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_roseStep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists
