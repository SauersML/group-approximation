import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# The extremal-region witness from walk sides and three junctions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-09.

* `RoseExtremalJunctionStatement` (OPEN, PLAUSIBLE; the isolated planarity core of the rose step):
  `P10RoseExtremal.RoseExtremalRegionStatement` with the clause
  `(s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts).IsChain R` replaced by "`s₁` and `s₂` are walks
  and the three junctions `s₁ | t₁⁻¹`, `s₁ t₁⁻¹ | s₂`, `s₁ t₁⁻¹ s₂ | t₂` meet at a vertex".
* `extremalRegion_of_junction` (part (a), proved): the walk property inside the blocks `t₁⁻¹`, `t₂`
  is discharged unconditionally by `P10RoseExtremalTrim.isChain_listing_of_junctions` (arcs of
  closed walks are walks, a walk read backwards is a walk).
* `singleRegionMove_of_junction`, `rose_of_junction`, `Piece10.proof_of_extremalJunction`: the
  single-region move, the rose step and the outer-pinch step from the residual, through
  `P10RoseExtremal.singleRegionMove_of_extremalRegion` (which proves the fourth junction `t₂ | s₁`
  by balance).
* `junction_of_extremalRegion`: the residual follows from `RoseExtremalRegionStatement`, so it is
  exactly as plausible as that statement and the target `P10Rose.RoseSingleRegionMoveStatement`.

## Why the residual is strictly smaller in proof content, and true when the old one is

A witness of the old statement gives one of the new statement by `List.isChain_append`
(`junction_of_extremalRegion`).  The new statement asks for the same witness `r`, cells, arcs and
short sides, but of the four blocks only the two free blocks `s₁`, `s₂` must be shown to be walks:
the walk property of `t₁⁻¹` and `t₂` (a sub-arc of a rotated closed walk, and its reversal) is
proved here and no longer part of the gap.  Together with `P10RoseExtremal/Close`, of the whole
closed-walk clause of the target only the free sides and three junctions remain.

## Part (b): the planarity core (not closed)

What remains is exactly the planarity content of Osin's choice of `Γ_1`.  Two ingredients are not
derivable from the combinatorial-map facts on disk:

1. *An extremal region meets the arcs in a prefix, a suffix or a whole arc.*  The flip-move API
   (`P10Rose.FilterMove.isBoundaryDart_flipFaces_iff`, module `P10Rose/Live/Move`) identifies the
   kept darts of the move by `regionColour r` with the boundary darts of the flipped face set, but
   it only speaks about membership, never about the order of the darts along
   `K.boundary.cycle = firstSide ++ t₁⁻¹ ++ secondSide ++ t₂`.  Relating the face classes of
   `FaceClassStep (walkKeep c)` to contiguous blocks of `c` needs the rotation-system planarity
   of the rose (a Jordan curve argument on the plane Eulerian graph of the cycle; the corpus tool
   `PassagesNoninterleaving`, module `NoncrossingClosedWalkEulerNoninterleaving`, is stated for
   noninterleaving passages, whereas the rose configuration `AllNonFirstTurnsCrossed` is the case
   where turns are crossed).
2. *The kept darts outside the arcs can be ordered as two walks `s₁`, `s₂` of length at most `ε`
   meeting the arcs at their ends.*  After (1), the kept darts outside `t₁⁻¹`, `t₂` lie in
   `firstSide`, `secondSide` and the facial walk of the removed region; the length bound needs that
   the removed region absorbs the sides of the flower except at most `ε` darts on each side.

Evidence (not a proof): the exhaustive search on rose configurations with at most five walk darts
and about a hundred random ones with six to twelve darts (module docstring of
`P10RoseEndpoint/SingleRegion`); the three-petal flower has the witness `s₁ = [p₃]`, `t₁' = t₁`,
`s₂ = [p₁, q₁]`, `t₂' = zeroArc t₂`, which satisfies the junction form directly.

## Imports

Reaches the live chain through `P10RoseExtremal/Reduction`; never imports `P10Rose/SubArcMove`,
`P10Rose/FilterMove` or `P10RoseKeptBalance/Kept` (name collisions).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

-- LOUD: REFUTED (lane gl-p10-48; Python model, not yet in Lean).
-- `RoseExtremalJunctionStatement` is FALSE:
-- it fails on the gl-p10-40 G-face model with
-- the label-1 edges subdivided once (24 darts).  Corrected residual:
-- `P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement` (`JunctionCore.lean`).
/-- **An extremal-region witness with walk sides and three junctions** (OPEN, PLAUSIBLE; the
isolated planarity core of the rose step).  `P10RoseExtremal.RoseExtremalRegionStatement` with the
walk clause of the listing replaced by: `s₁`, `s₂` are walks and the junctions `s₁ | t₁⁻¹`,
`s₁ t₁⁻¹ | s₂`, `s₁ t₁⁻¹ s₂ | t₂` meet at a vertex. -/
def RoseExtremalJunctionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart,
          (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
          (∃ y ∈ K.boundary.cycle, Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
            Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
              (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
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

/-- **The extremal-region witness from walk sides and three junctions**: the blocks `t₁⁻¹` and
`t₂` are walks, so the listing is a walk. -/
theorem extremalRegion_of_junction (h : RoseExtremalJunctionStatement.{u, w, v}) :
    P10RoseExtremal.RoseExtremalRegionStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, hry, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hne, hs₁c, hs₂c,
    hj₁, hj₂, hj₃, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, hrout, hry, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hne,
    isChain_listing_of_junctions t₁ t₂ hs₁c hs₂c hj₁ hj₂ hj₃, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

/-- **The residual is implied by the extremal-region witness** (truth certificate of the residual:
it is exactly as plausible as `RoseExtremalRegionStatement`). -/
theorem junction_of_extremalRegion (h : P10RoseExtremal.RoseExtremalRegionStatement.{u, w, v}) :
    RoseExtremalJunctionStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, hry, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hne, hchain,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨hs₁c, hs₂c, hj₁, hj₂, hj₃⟩ := junctions_of_isChain_listing t₁ t₂ hchain
  exact ⟨r, hrout, hry, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hne, hs₁c, hs₂c,
    hj₁, hj₂, hj₃, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

/-- **The single-region move from walk sides and three junctions.** -/
theorem singleRegionMove_of_junction (h : RoseExtremalJunctionStatement.{u, w, v}) :
    P10Rose.RoseSingleRegionMoveStatement.{u, w, v} :=
  P10RoseExtremal.singleRegionMove_of_extremalRegion (extremalRegion_of_junction h)

/-- **The rose step from walk sides and three junctions.** -/
theorem rose_of_junction (h : RoseExtremalJunctionStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  P10RoseExtremal.rose_of_extremalRegion (extremalRegion_of_junction h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

/-- **The outer-pinch step from walk sides and three junctions.** -/
theorem proof_of_extremalJunction
    (h : P10RoseExtremalTrim.RoseExtremalJunctionStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_extremalRegion (P10RoseExtremalTrim.extremalRegion_of_junction h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.extremalRegion_of_junction
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.junction_of_extremalRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.singleRegionMove_of_junction
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.rose_of_junction
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_extremalJunction
