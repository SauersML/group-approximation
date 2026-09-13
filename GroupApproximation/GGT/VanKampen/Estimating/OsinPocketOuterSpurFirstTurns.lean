import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterSpur
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoublingFirstTurns
import GroupApproximation.Meta.AxiomGuard

/-!
# First-turn order survives the thickening of an outer spur

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The pinch step for a pocket face set in first-turn order splits a vertex
at two gap corners, and a gap corner in the exterior is first filled with a G-cell digon by
thickening an outer edge (`PocketFaceSet.outerSpurThickening`, `Estimating/OsinPocketOuterSpur.lean`).
The thickening is known to keep walk order and repeated visits.  This module shows that it keeps
first-turn order as well.

The thickened map `OuterSpurThickening.diagram X j hlen` is the doubling of an edge of the exterior,
`FaceEdgeDoubling.map X X.outerFace j hlen`, which is the edge insertion
`EdgeInsertion.toCombMap` at the corners `w_j` and `w_{j+1}` of the rebased exterior traversal.  The
corners are distinct (`EdgeInsertion.corners_ne` at index `1 < |∂X|`).  The boundary cycle of the
thickened pocket is the old cycle under the dart embedding `EdgeInsertion.embed`
(`PocketFaceSet.outerSpurThickening_boundary_cycle`).  So the first-turn chain lifts by
`EdgeInsertion.firstTurnChain_map_embed` (`Estimating/OsinPocketEdgeDoublingFirstTurns.lean`), the
same lift that serves the doublings outside and inside the face set.

* `PocketFaceSet.outerSpurThickening_firstTurnChain`: across the thickening of an outer edge.
* `PocketOuterSpurFirstTurnChainStatement`, `pocketOuterSpurFirstTurnChain`: the same, as a closed
  proposition.

The first-turn chain is stated inline, in the spelling of `firstTurnWalkPocketInputs` on the
complement walk `cycle.reverse.map alpha`, as in `PocketFaceSet.faceEdgeDoubling_firstTurnChain`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv SimpleClosedWalkSides

universe u w v

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The thickening of an outer spur keeps first-turn order.** -/
theorem outerSpurThickening_firstTurnChain (K : PocketFaceSet D eps X lo hi)
    (j : Fin (X.faceBoundary X.outerFace).darts.length)
    (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)
    (htgt : X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j) ∉ K.targetArc.darts)
    (hK : K.boundary.cycle.IsChain (fun d e => FirstTurn X.toCombMap
          (K.boundary.cycle.reverse.map X.toCombMap.alpha) (X.toCombMap.alpha e)
          (X.toCombMap.alpha d)) ∧
        FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
          (X.toCombMap.alpha (K.boundary.cycle.head K.boundary.cycle_nonempty))
          (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))) :
    (K.outerSpurThickening j hlen htgt).boundary.cycle.IsChain (fun d e =>
        FirstTurn (OuterSpurThickening.diagram X j hlen).toCombMap
          ((K.outerSpurThickening j hlen htgt).boundary.cycle.reverse.map
            (OuterSpurThickening.diagram X j hlen).toCombMap.alpha)
          ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha e)
          ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha d)) ∧
      FirstTurn (OuterSpurThickening.diagram X j hlen).toCombMap
        ((K.outerSpurThickening j hlen htgt).boundary.cycle.reverse.map
          (OuterSpurThickening.diagram X j hlen).toCombMap.alpha)
        ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha
          ((K.outerSpurThickening j hlen htgt).boundary.cycle.head
            (K.outerSpurThickening j hlen htgt).boundary.cycle_nonempty))
        ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha
          ((K.outerSpurThickening j hlen htgt).boundary.cycle.getLast
            (K.outerSpurThickening j hlen htgt).boundary.cycle_nonempty)) :=
  EdgeInsertion.firstTurnChain_map_embed
    (EdgeInsertion.corners_ne X.toCombMap (FaceEdgeDoubling.rebased X X.outerFace j)
      (FaceEdgeDoubling.second X X.outerFace j hlen) Nat.one_pos)
    K.boundary.cycle_nonempty (K.outerSpurThickening j hlen htgt).boundary.cycle_nonempty hK

end PocketFaceSet

/-- **First-turn order across the thickening of an outer spur.**  A pocket face set in first-turn
order, whose target arc avoids the reverse `α w_j` of an outer edge, keeps first-turn order when
that outer edge is thickened into a G-cell digon. -/
def PocketOuterSpurFirstTurnChainStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ)
    (K : PocketFaceSet D eps X lo hi) (j : Fin (X.faceBoundary X.outerFace).darts.length)
    (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)
    (htgt : X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j) ∉ K.targetArc.darts),
    (K.boundary.cycle.IsChain (fun d e => FirstTurn X.toCombMap
          (K.boundary.cycle.reverse.map X.toCombMap.alpha) (X.toCombMap.alpha e)
          (X.toCombMap.alpha d)) ∧
        FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
          (X.toCombMap.alpha (K.boundary.cycle.head K.boundary.cycle_nonempty))
          (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))) →
      (K.outerSpurThickening j hlen htgt).boundary.cycle.IsChain (fun d e =>
          FirstTurn (OuterSpurThickening.diagram X j hlen).toCombMap
            ((K.outerSpurThickening j hlen htgt).boundary.cycle.reverse.map
              (OuterSpurThickening.diagram X j hlen).toCombMap.alpha)
            ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha e)
            ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha d)) ∧
        FirstTurn (OuterSpurThickening.diagram X j hlen).toCombMap
          ((K.outerSpurThickening j hlen htgt).boundary.cycle.reverse.map
            (OuterSpurThickening.diagram X j hlen).toCombMap.alpha)
          ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha
            ((K.outerSpurThickening j hlen htgt).boundary.cycle.head
              (K.outerSpurThickening j hlen htgt).boundary.cycle_nonempty))
          ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha
            ((K.outerSpurThickening j hlen htgt).boundary.cycle.getLast
              (K.outerSpurThickening j hlen htgt).boundary.cycle_nonempty))

theorem pocketOuterSpurFirstTurnChain : PocketOuterSpurFirstTurnChainStatement.{u, w, v} := by
  intro G _ Lambda D eps W X lo hi K j hlen htgt hK
  exact K.outerSpurThickening_firstTurnChain j hlen htgt hK

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.outerSpurThickening_firstTurnChain
#audit_closed_axioms GroupApproximation.GGT.VanKampen.pocketOuterSpurFirstTurnChain
