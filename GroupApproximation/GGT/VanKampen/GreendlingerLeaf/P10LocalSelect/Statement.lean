import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.Inside
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.Outside
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantSelect.Move
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantSelect.MoveCut
import GroupApproximation.Meta.AxiomGuard

/-!
# The local selection of a lobe for the quadrant move (interface)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

The quadrant move `P10FilterMoveExists.p10FM_QuadrantMoveStatement` has eight proved witness
lemmas, each for a given list `B ⊆ c` under explicit hypotheses:
* one-sided cyclic blocks: `P10QuadrantMove.p10QM_move_FF`, `_TF` (rest of `c` on the side),
  `_TT`, `_FT` (rest off the side, arcs off `B`);
* lobes untouched away from one vertex: `p10QS_move_untouched_FF`, `_TF` (some rest dart on the
  side), `_TT`, `_FT` (some rest dart off the side, arc clauses given).
`p10LS_Good` is the disjunction of their hypothesis bundles, with the ambient hypotheses of the
quadrant move removed.  `p10LS_SelectionStatement` says that under the hypotheses of the quadrant
move some `B` is good.

* Step 2, the selection by induction on passages: prove `p10LS_SelectionStatement`.
* Step 3, the quadrant move from the selection: `p10LS_SelectionStatement →
  p10FM_QuadrantMoveStatement`, by case analysis on `p10LS_Good` and the eight lemmas.

The paper proof of step 2 is by lanes ms-nm-partial-a and nm-gl03d (swarm board nm-gl03d).  This
module holds the statements only.  `p10LS_SelectionStatement` is **OPEN**.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists
  P10QuadrantMove

/-- **A good lobe** `B` for the quadrant move: the case-specific hypotheses of one of the eight
proved witness lemmas.  The first four cases are the one-sided cyclic blocks, the last four the
lobes untouched away from a vertex `v0`. -/
def p10LS_Good (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F) (o s k : M.Face)
    (A T : List M.Dart) (B : List M.Dart) : Prop :=
  -- `p10QM_move_FF` / `p10QM_move_TF`: `B` a simple cyclic block, the rest of `c` on its side.
  (p10QM_CyclicBlock c.cycle B ∧ IsSimpleClosedWalk M B ∧ (∃ d ∈ c.cycle, d ∉ B) ∧
    (∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∈ sideFaces M B) ∧
    ((o ∈ sideFaces M B ∧ s ∈ sideFaces M B) ∨ (o ∉ sideFaces M B ∧ s ∉ sideFaces M B))) ∨
  -- `p10QM_move_TT` / `p10QM_move_FT`: `B` a closed cyclic block, the rest of `c` off its side,
  -- both arcs off `B`.
  (p10QM_CyclicBlock c.cycle B ∧ IsClosedDartWalk M B ∧ (∃ d ∈ c.cycle, d ∉ B) ∧
    (∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∉ sideFaces M B) ∧
    (∀ d ∈ A, d ∉ B) ∧ (∀ d ∈ T, d ∉ B)) ∨
  -- `p10QS_move_untouched_FF` / `_TF`: an untouched simple lobe with a rest dart on its side.
  (IsSimpleClosedWalk M B ∧ (∀ e ∈ B, e ∈ c.cycle) ∧
    (∃ v0 : M.Vertex, p10QS_Untouched M c.cycle B v0) ∧
    (∃ d ∈ c.cycle, d ∉ B ∧ M.faceOf d ∈ sideFaces M B) ∧
    ((o ∈ sideFaces M B ∧ s ∈ sideFaces M B) ∨ (o ∉ sideFaces M B ∧ s ∉ sideFaces M B))) ∨
  -- `p10QS_move_untouched_TT` / `_FT`: an untouched simple lobe with a rest dart off its side, and
  -- the arc clauses of the quadrant `p = [k ∉ side B]`, `q = true`.
  (IsSimpleClosedWalk M B ∧ (∀ e ∈ B, e ∈ c.cycle) ∧
    (∃ v0 : M.Vertex, p10QS_Untouched M c.cycle B v0) ∧
    (∃ d ∈ c.cycle, d ∉ B ∧ M.faceOf d ∉ sideFaces M B) ∧
    ((k ∉ sideFaces M B ∧
        A.filter (movePred M (p10FM_z M F B true true)) <:+: A ∧
        T.filter (movePred M (p10FM_z M F B true true)) <+: T) ∨
      (k ∈ sideFaces M B ∧
        A.filter (movePred M (p10FM_z M F B false true)) <:+: A ∧
        T.filter (movePred M (p10FM_z M F B false true)) <+: T)))

/-- **The local selection statement** (OPEN; step 2).  Under the hypotheses of
`P10FilterMoveExists.p10FM_QuadrantMoveStatement`, some list `B` of darts is a good lobe. -/
def p10LS_SelectionStatement : Prop :=
  ∀ (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F) (o s k : M.Face)
    (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ : List M.Dart),
    M.IsPlanar → IsClosedDartWalk M c.cycle → ¬Unpinched M F →
    ¬p10FM_FirstTurns M c.cycle c.cycle_nonempty → p10FM_AllCrossed M c.cycle →
    o ∉ F → s ∉ F → s ≠ o → k ∈ F →
    a.length < bs.darts.length → b.length < (bo.darts.reverse.map M.alpha).length →
    c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts →
    ∃ B : List M.Dart, p10LS_Good M F c o s k (a.darts.reverse.map M.alpha) b.darts B

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_Good
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_SelectionStatement
