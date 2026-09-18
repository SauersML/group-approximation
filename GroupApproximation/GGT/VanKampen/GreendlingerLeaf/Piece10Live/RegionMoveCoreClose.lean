import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveCoreCloseTight
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AssemblyResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# The extremal-region core at a loose crossing

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-19.

## Choice of residual

`RoseExtremalCoreStatement` is already reduced by proved `_of_` theorems to statements owned by the
sibling lanes:
* Core ← Contiguity ← ContigResidual ← `RoseExtremalBlockStatement` ←
  `RoseExtremalBlockCoreStatement` (gl-p10-18).
* The no-wrap chain ends at `RoseExtremalBlockNoWrapCoreStatement` (gl-p10-18), then
  `RoseExtremalRegionStatement` ← `RoseExtremalClassStatement` ← `ExtremalMinimalUniformStatement`
  (gl-p10-17).

Every other open `*Statement` of `Piece10Live` on the path to the Greendlinger leaf reduces to
these.  So this lane does not re-reduce Core through any of those chains.  It works on the premise block of
Core instead, and records the combinatorial content of the rose premises.

## Route

* `RegionMoveCoreCloseStatement` (OPEN): `RoseExtremalCoreStatement` with the extra premise
  `RegionMoveCoreCloseLooseCross K`.  The pocket has a non-first turn `d₀ → next d₀` with
  `σ (next d₀) ≠ α d₀`, crossed by a passage `d ≠ d₀` with `σ (next d) ≠ α d`.
* `regionMoveCoreClose_extremalCore_of_close` (proved): Close → Core, by
  `regionMoveCoreClose_looseCross` (module `RegionMoveCoreCloseTight`).
* `regionMoveCoreClose_close_of_extremalCore` (proved): Core → Close (truth certificate).
* `regionMoveCoreClose_step_of_close` (proved): `PocketOuterPinchStepSectionStatement`.
* `regionMoveCoreClose_relativeGreendlinger_of_close` (proved): the Greendlinger leaf, from
  `P07InnerPocket.PocketFourPieceOffStatement` and Close.

## Status of the residual (LOUD)

Close is **logically equivalent** to Core, because the extra premise follows from the rose premises
(`regionMoveCoreClose_looseCross`).  It is not a restatement.  It is **strictly smaller in proof
content**: a proof of Close may use a loose crossing that a proof of Core must first construct.
That construction is proved here (`σ`-injectivity plus the fact that `α` of a boundary dart is off
the boundary).  The case of at most one loose passage, where the rose premises are contradictory,
is discharged here.  One instance is `ε = 0` with one arc empty, since every passage inside an arc
is tight.

## Truth check

Close is implied by Core (`regionMoveCoreClose_close_of_extremalCore`), so it is as plausible as
Core: no counterexample is known (docstring of `RegionMoveCore`).  The GL05c counterexample refutes
only the single-region end-block form `ExtremalEndBlockStatement`, not Core.

## Remaining gap

Close itself.  The next honest cut is `ε = 0` with both arcs nonempty.  There the loose passages
are exactly the two junctions.  Membership in `F` alternates around the vertex of a junction, so
the passages with one end inside its sector pair up, and the other junction cannot be the only
crosser.  So that case is also vacuous, but it needs an orbit-counting argument that is not
formalized here.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

-- LOUD: REFUTED (lane gl-p10-48; Python model, not yet in Lean).
-- `RegionMoveCoreCloseStatement` is FALSE:
-- it implies `RoseExtremalJunctionStatement`, which fails on the gl-p10-40 G-face model with
-- the label-1 edges subdivided once (24 darts).  Corrected residual:
-- `P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement` (`JunctionCore.lean`).
/-- **The extremal-region core at a loose crossing** (OPEN, PLAUSIBLE): `RoseExtremalCoreStatement`
with the extra premise `RegionMoveCoreCloseLooseCross K`, which `regionMoveCoreClose_looseCross`
derives from the rose premises. -/
def RegionMoveCoreCloseStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      RegionMoveCoreCloseLooseCross K →
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

/-- **The core from the core at a loose crossing**: the rose premises give the loose crossing. -/
theorem regionMoveCoreClose_extremalCore_of_close (h : RegionMoveCoreCloseStatement.{u, w, v}) :
    RoseExtremalCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
    (regionMoveCoreClose_looseCross K hnft hrose)

/-- **The core at a loose crossing from the core** (truth certificate of the residual). -/
theorem regionMoveCoreClose_close_of_extremalCore (h : RoseExtremalCoreStatement.{u, w, v}) :
    RegionMoveCoreCloseStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose _
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose

/-- **The outer-pinch step from the core at a loose crossing.** -/
theorem regionMoveCoreClose_step_of_close (h : RegionMoveCoreCloseStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  Piece10.proof_of_extremalCore (regionMoveCoreClose_extremalCore_of_close h)

/-- **The Greendlinger leaf from the core at a loose crossing**, with the four-piece-off
residual of binder 7. -/
theorem regionMoveCoreClose_relativeGreendlinger_of_close
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : RegionMoveCoreCloseStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  AssemblyResidual.relativeGreendlinger_of_residuals hoff
    (extremalJunction_of_extremalCore (regionMoveCoreClose_extremalCore_of_close h))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveCoreCloseStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveCoreClose_extremalCore_of_close
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveCoreClose_close_of_extremalCore
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveCoreClose_step_of_close
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveCoreClose_relativeGreendlinger_of_close
