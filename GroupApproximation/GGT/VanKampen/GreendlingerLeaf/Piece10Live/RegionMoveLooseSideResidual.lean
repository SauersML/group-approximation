import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseSideCross
import GroupApproximation.Meta.AxiomGuard

/-!
# The core at a loose crossing with two loose crossers of one turn

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-23.

## Route

* `regionMoveLooseSide_cross_of_looseCross` (proved, module `RegionMoveLooseSideCross`): a loose
  crossing `(d₀, d)` has a second loose crosser `e ∉ {d₀, d}` of the same turn `d₀`, with `α e`
  in the rotation orbit of `α d₀`.  One of `d₀, d, e` starts in a side `s₁` or `s₂`.
* `RegionMoveLooseSideStatement` (OPEN, PLAUSIBLE): `RegionMoveLooseResidualStatement` with its
  premise `RegionMoveLooseThree K` replaced by the stronger `RegionMoveLooseSideCross K`.
* `regionMoveLooseResidual_of_side` (proved): Side → Residual.
* `regionMoveLooseSide_of_residual` (proved): Residual → Side (truth certificate).
* `regionMoveLooseSide_close_of_side`, `regionMoveLooseSide_extremalCore_of_side` (proved).

## Status of the residual (LOUD)

`RegionMoveLooseSideStatement` is **logically equivalent** to `RegionMoveLooseResidualStatement`,
to `RegionMoveCoreCloseStatement` and to `RoseExtremalCoreStatement`: its extra premise follows
from the premises of the residual.  It is **strictly smaller in proof content**.  A proof may
assume more than the residual allows:
* the third loose passage `e` also crosses the turn `d₀`, not just some unrelated passage;
* `e` sits at the vertex of the turn (`SameCycle (α d₀) (α e)`);
* one of the three loose passages `d₀, d, e` starts in a side `s₁` or `s₂`, not at a junction.
Those three facts are proved here: the crossing parity (the crossers of a turn are even in number)
and the pigeonhole on the two junctions.  It is not strictly weaker in logical strength: no
nonvacuous case of Close is discharged outright.

## Truth check

Implied by the residual (`regionMoveLooseSide_of_residual`), hence by Close and Core.  So it is as
plausible as Core: no counterexample is known (docstring of `RegionMoveCore`).  The one-vertex
Python model (`scratchpad/gl-p10-23/model.py`) confirms the combinatorial refinement:
12200 loose crossings checked, each with a second loose crosser.  The model also shows that the
crosser `d` need not cross `e`, so a "triangle" of pairwise crossings is NOT claimed.  It avoids
the refuted forms `ExtremalEndBlockStatement`, `FrameConeFourStatement` and the
`PocketFourPiece*` witness statements.

## Remaining gap

The statement itself: build the region `r` and the decomposition `s₁ t₁ s₂ t₂` of the kept
boundary in a pocket with `ε > 0`, whose turn `d₀` has two loose crossers at its vertex.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

/-- **The core at a loose crossing with two loose crossers of one turn** (OPEN, PLAUSIBLE; LOUD:
logically equivalent to `RegionMoveLooseResidualStatement` and to `RegionMoveCoreCloseStatement`,
strictly smaller in proof content): the residual with `RegionMoveLooseThree K` strengthened to
`RegionMoveLooseSideCross K`. -/
def RegionMoveLooseSideStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      RegionMoveCoreCloseLooseCross K →
      0 < eps → (K.firstSide ≠ [] ∨ K.secondSide ≠ []) → RegionMoveLooseSideCross K →
        ∃ r : X.toCombMap.Dart,
          (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
          ∃ (source kept : Fin X.rCellCount),
            (cell X source).face ∉ flipFaces X.toCombMap K.faces
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
            (cell X kept).face ∈ flipFaces X.toCombMap K.faces
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
            ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
              (s₁ s₂ : List X.toCombMap.Dart),
              List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
                (K.boundary.cycle.filter (movePred X.toCombMap
                  (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))) ∧
              s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ≠ [] ∧
              (s₁.IsChain fun d e =>
                X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
              (s₂.IsChain fun d e =>
                X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
              (∀ a ∈ s₁.getLast?, ∀ b ∈ (invDarts X t₁.darts).head?,
                X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
              (∀ a ∈ (s₁ ++ invDarts X t₁.darts).getLast?, ∀ b ∈ s₂.head?,
                X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
              (∀ a ∈ (s₁ ++ invDarts X t₁.darts ++ s₂).getLast?, ∀ b ∈ t₂.darts.head?,
                X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
              s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi ∧
              t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

/-- **The residual from the side statement**: the loose crossing refines to a side crossing. -/
theorem regionMoveLooseResidual_of_side (h : RegionMoveLooseSideStatement.{u, w, v}) :
    RegionMoveLooseResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hloose hε hs _
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hloose hε hs
    (regionMoveLooseSide_cross_of_looseCross K hK hloose)

/-- **The side statement from the residual** (truth certificate). -/
theorem regionMoveLooseSide_of_residual (h : RegionMoveLooseResidualStatement.{u, w, v}) :
    RegionMoveLooseSideStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hloose hε hs hsc
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hloose hε hs
    (regionMoveLooseSide_three_of_cross K hsc)

/-- **Close from the side statement.** -/
theorem regionMoveLooseSide_close_of_side (h : RegionMoveLooseSideStatement.{u, w, v}) :
    RegionMoveCoreCloseStatement.{u, w, v} :=
  regionMoveLoose_close_of_residual (regionMoveLooseResidual_of_side h)

/-- **The extremal-region core from the side statement.** -/
theorem regionMoveLooseSide_extremalCore_of_side (h : RegionMoveLooseSideStatement.{u, w, v}) :
    RoseExtremalCoreStatement.{u, w, v} :=
  regionMoveLoose_extremalCore_of_residual (regionMoveLooseResidual_of_side h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveLooseSideStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseResidual_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_of_residual
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_close_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_extremalCore_of_side
