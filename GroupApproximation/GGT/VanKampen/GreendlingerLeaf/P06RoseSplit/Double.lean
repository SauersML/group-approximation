import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseSplit.Criterion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefineStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoubling
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, rose split: one and two edge doublings as redraws

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining two cells.

The proposed redraw of an uncut rose doubles an edge of cell `i` and one of cell `j`
(`FaceEdgeDoubling`, an inner face each time) and looks for a competitor `K₂` with a turn split
in the result.  This file proves the parts of that route that hold in every configuration:

* `p06RoseSplit_dblRedraw`: one doubling of an inner face is an O-equivalent redraw with
  letter labels of the symmetrized alphabet;
* `p06RoseSplit_dbl2Redraw`: so are two successive doublings, which keep the number of relator
  cells;
* `p06RoseSplit_dbl2Split`: a turn-split competitor in a double doubling refutes
  `p06RoseDecide_RedrawStuck K`;
* `p06RoseSplit_dblPocket`, `p06RoseSplit_dblStuck`: the transported pocket
  `K.faceEdgeDoubling` (a face outside `K.faces`, a dart on neither arc) keeps distinct cells,
  walk order, proper arcs and repeated visits, and stays stuck in every redraw.

## Where the route stops

The competitor `K₂` itself is not constructed.  Its shape depends on the configuration (see the
truth check in `P06RoseSplit/Criterion`).  With both arcs touching the pinch vertex and
`eps ≥ 2`, `K₂` has faces `{k, D_r, D_h}`.  With `eps = 1` only one side can be doubled.  If an
arc misses the pinch vertex, the doubling must be inside a G-petal instead.  If neither arc
touches the pinch vertex (model 3), no redraw by at most two doublings has a turn split.

Note that `p06RoseSplit_dblStuck` does **not** apply to the doublings of the proposed route.
Those double an *arc* dart of cell `i` or `j`, which `K.faceEdgeDoubling` excludes
(`hfirst`, `hsecond`).  After such a doubling `K` is not carried over, and `K₂` has to be built
directly with `CellPocketFaceSet.ofBoundaryCycle`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

section Double

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

variable (X : DiscDiagram.{u, w, v} W) (f : X.toCombMap.Face)
  (k : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
  (hf : f ≠ X.outerFace)

/-- **One doubling is a redraw**: O-equivalent, with letter labels. -/
theorem p06RoseSplit_dblRedraw
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) :
    Nonempty (OEquivalentDiscDiagram X (FaceEdgeDoubling.diagram X f k hlen hf)) ∧
      ∀ d, (symmetricLabelAlphabet D).IsLetter
        ((FaceEdgeDoubling.diagram X f k hlen hf).label d) :=
  ⟨⟨FaceEdgeDoubling.oEquivalent X f k hlen hf⟩,
    FaceEdgeDoubling.label_letter X f k hlen hf hlabel⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_dblRedraw

variable (f₂ : (FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.Face)
  (k₂ : Fin ((FaceEdgeDoubling.diagram X f k hlen hf).faceBoundary f₂).darts.length)
  (hlen₂ : 1 < ((FaceEdgeDoubling.diagram X f k hlen hf).faceBoundary f₂).darts.length)
  (hf₂ : f₂ ≠ (FaceEdgeDoubling.diagram X f k hlen hf).outerFace)

/-- **Two doublings are a redraw**: O-equivalent, with letter labels and as many relator
cells. -/
theorem p06RoseSplit_dbl2Redraw
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) :
    Nonempty (OEquivalentDiscDiagram X
        (FaceEdgeDoubling.diagram (FaceEdgeDoubling.diagram X f k hlen hf) f₂ k₂ hlen₂ hf₂)) ∧
      (∀ d, (symmetricLabelAlphabet D).IsLetter
        ((FaceEdgeDoubling.diagram (FaceEdgeDoubling.diagram X f k hlen hf) f₂ k₂ hlen₂
          hf₂).label d)) ∧
      (FaceEdgeDoubling.diagram (FaceEdgeDoubling.diagram X f k hlen hf) f₂ k₂ hlen₂
        hf₂).rCellCount = X.rCellCount :=
  ⟨⟨OEquivalentDiscDiagram.trans (FaceEdgeDoubling.oEquivalent X f k hlen hf)
      (FaceEdgeDoubling.oEquivalent _ f₂ k₂ hlen₂ hf₂)⟩,
    FaceEdgeDoubling.label_letter _ f₂ k₂ hlen₂ hf₂
      (FaceEdgeDoubling.label_letter X f k hlen hf hlabel),
    (FaceEdgeDoubling.rCellCount_eq _ f₂ k₂ hlen₂ hf₂).trans
      (FaceEdgeDoubling.rCellCount_eq X f k hlen hf)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_dbl2Redraw

/-- **A turn-split competitor after two doublings refutes stuck in every redraw.** -/
theorem p06RoseSplit_dbl2Split {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {i₂ j₂ : Fin (FaceEdgeDoubling.diagram (FaceEdgeDoubling.diagram X f k hlen hf) f₂ k₂
      hlen₂ hf₂).rCellCount}
    (K₂ : CellPocketFaceSet D eps
      (FaceEdgeDoubling.diagram (FaceEdgeDoubling.diagram X f k hlen hf) f₂ k₂ hlen₂ hf₂) i₂ j₂)
    (hij : i₂ ≠ j₂) (hK : K₂.ClosedWalk)
    (hfirst : K₂.firstArc.length < (cellDarts
      (FaceEdgeDoubling.diagram (FaceEdgeDoubling.diagram X f k hlen hf) f₂ k₂ hlen₂ hf₂)
        i₂).length)
    (hsecond : K₂.secondArc.length < (cellDarts
      (FaceEdgeDoubling.diagram (FaceEdgeDoubling.diagram X f k hlen hf) f₂ k₂ hlen₂ hf₂)
        j₂).length)
    (hle : K₂.repeatedVisits ≤ K.repeatedVisits) (hsplit : p06RoseRedraw_TurnSplit K₂) :
    ¬ p06RoseDecide_RedrawStuck K :=
  p06RoseSplit_ofTurnSplit K (p06RoseSplit_dbl2Redraw X f k hlen hf f₂ k₂ hlen₂ hf₂ hlabel).1
    (p06RoseSplit_dbl2Redraw X f k hlen hf f₂ k₂ hlen₂ hf₂ hlabel).2.1 K₂ hij hK hfirst hsecond
    hle hsplit

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_dbl2Split

end Double

section Transport

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

variable {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j)
  (f : X.toCombMap.Face) (k : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace) (hs : f ∉ K.faces)
  (hfirst : FaceEdgeDoubling.dart X f k ∉ K.firstArc.darts)
  (hsecond : FaceEdgeDoubling.dart X f k ∉ K.secondArc.darts)

/-- **The transported pocket is again a competitor**: distinct cells, walk order, proper arcs and
the same repeated visits, across a doubling off the face set and off both arcs. -/
theorem p06RoseSplit_dblPocket (hij : i ≠ j) (hK : K.ClosedWalk)
    (hfirstP : K.firstArc.length < (cellDarts X i).length)
    (hsecondP : K.secondArc.length < (cellDarts X j).length) :
    (FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv i ≠
        (FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv j ∧
      (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).ClosedWalk ∧
      (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).firstArc.length <
        (cellDarts (FaceEdgeDoubling.diagram X f k hlen hf)
          ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv i)).length ∧
      (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).secondArc.length <
        (cellDarts (FaceEdgeDoubling.diagram X f k hlen hf)
          ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv j)).length ∧
      (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).repeatedVisits = K.repeatedVisits :=
  ⟨fun h => hij ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv.injective h),
    K.faceEdgeDoubling_closedWalk f k hlen hf hs hfirst hsecond hK,
    CornerRefine.inner_first_proper X f k hlen K hf hs hfirst hsecond hfirstP,
    CornerRefine.inner_second_proper X f k hlen K hf hs hfirst hsecond hsecondP,
    K.faceEdgeDoubling_repeatedVisits f k hlen hf hs hfirst hsecond⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_dblPocket

/-- **Stuck in every redraw survives the transport** across a doubling off the face set and off
both arcs. -/
theorem p06RoseSplit_dblStuck (h : p06RoseDecide_RedrawStuck K) :
    p06RoseDecide_RedrawStuck (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond) :=
  p06RoseSplit_ofOEquiv h ⟨FaceEdgeDoubling.oEquivalent X f k hlen hf⟩ _
    (K.faceEdgeDoubling_repeatedVisits f k hlen hf hs hfirst hsecond).le

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_dblStuck

end Transport

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06
