import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# Good lobes that meet the arcs (interface)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

The one-sided witness lemmas `P10QuadrantMove.p10QM_move_TT` / `_FT` need both arcs off the lobe
`B`.  The local selection also picks lobes that meet the arcs in end blocks: the stretch of the
kept cell's piece holds one end of each arc.  `p10LS_GoodArc` is that case.  `B` is a closed
cyclic block with the rest of `c` off its side, and the arcs are cut by `B` so that the kept part
is an infix of `a⁻¹` and a prefix of `b`:
* `k ∉ side B`, quadrant `p = q = true`: the move removes exactly `B`, so the kept parts are the
  arc darts off `B`;
* `k ∈ side B`, quadrant `p = false, q = true`: the move keeps exactly `B`, so the kept parts are
  the arc darts on `B`.

* `p10LS_GoodArc`: the case.
* `p10LS_SelectionArcStatement`: under the quadrant-move hypotheses, some `B` is `p10LS_Good` or
  `p10LS_GoodArc`.  It is implied by `p10LS_SelectionStatement` (`p10LS_selectionArc_of_selection`).

Statements only, apart from that implication.  The witness lemma for `p10LS_GoodArc` and the
selection itself are **OPEN**.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists
  P10QuadrantMove

open scoped Classical

/-- **A good lobe meeting the arcs**: a closed cyclic block `B` with the rest of `c` off its side,
cutting `A = a⁻¹` and `T = b` so that the kept parts are an infix of `A` and a prefix of `T`. -/
def p10LS_GoodArc (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F) (k : M.Face)
    (A T : List M.Dart) (B : List M.Dart) : Prop :=
  p10QM_CyclicBlock c.cycle B ∧ IsClosedDartWalk M B ∧ (∃ d ∈ c.cycle, d ∉ B) ∧
    (∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∉ sideFaces M B) ∧
    ((k ∉ sideFaces M B ∧
        A.filter (fun d => decide (d ∉ B)) <:+: A ∧ T.filter (fun d => decide (d ∉ B)) <+: T) ∨
      (k ∈ sideFaces M B ∧
        A.filter (fun d => decide (d ∈ B)) <:+: A ∧ T.filter (fun d => decide (d ∈ B)) <+: T))

/-- **The local selection with arc-meeting lobes** (OPEN).  Under the hypotheses of
`P10FilterMoveExists.p10FM_QuadrantMoveStatement`, some `B` is a good lobe or a good lobe meeting
the arcs. -/
def p10LS_SelectionArcStatement : Prop :=
  ∀ (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F) (o s k : M.Face)
    (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ : List M.Dart),
    M.IsPlanar → IsClosedDartWalk M c.cycle → ¬Unpinched M F →
    ¬p10FM_FirstTurns M c.cycle c.cycle_nonempty → p10FM_AllCrossed M c.cycle →
    o ∉ F → s ∉ F → s ≠ o → k ∈ F →
    a.length < bs.darts.length → b.length < (bo.darts.reverse.map M.alpha).length →
    c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts →
    ∃ B : List M.Dart,
      p10LS_Good M F c o s k (a.darts.reverse.map M.alpha) b.darts B ∨
        p10LS_GoodArc M F c k (a.darts.reverse.map M.alpha) b.darts B

/-- The selection gives the selection with arc-meeting lobes. -/
theorem p10LS_selectionArc_of_selection (h : p10LS_SelectionStatement.{v}) :
    p10LS_SelectionArcStatement.{v} := by
  intro M F c o s k bs bo a b s₁ s₂ hM hc hpin hft hac ho hs hso hk ha hb hsplit
  obtain ⟨B, hB⟩ := h M F c o s k bs bo a b s₁ s₂ hM hc hpin hft hac ho hs hso hk ha hb hsplit
  exact ⟨B, Or.inl hB⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_GoodArc
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_SelectionArcStatement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_selectionArc_of_selection
