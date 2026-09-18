import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal.Close
import GroupApproximation.Meta.AxiomGuard

/-!
# The single-region move from an extremal-region witness

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-08, part 2.

* `RoseExtremalRegionStatement` (OPEN, PLAUSIBLE): `P10Rose.RoseSingleRegionMoveStatement` with the
  clause `IsClosedDartWalk X.toCombMap L` (for `L = s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts`)
  replaced by `L ≠ [] ∧ L.IsChain (fun d e => vertexOf (alpha d) = vertexOf e)`.
* `singleRegionMove_of_extremalRegion`: the reduction.  The dropped closing equation
  `vertexOf (alpha (L.getLast _)) = vertexOf (L.head _)` is proved
  (`P10RoseExtremal.isClosedDartWalk_of_perm_filter`, module `P10RoseExtremal/Close`): the kept
  darts of the move by `z = regionColour r` are the boundary darts of the flipped face set, hence
  balanced at every vertex, and a balanced chain closes up.
* `rose_of_extremalRegion`, `Piece10.proof_of_extremalRegion`: the rose step and the outer-pinch
  step from the residual gap.

## Why the residual is strictly smaller in proof content

`RoseExtremalRegionStatement` asks for the same witness `r`, cells, arcs and short sides, and for
every clause of the target except the closing equation of the closed walk; that equation is
discharged here unconditionally (kept balance `P10RoseKeptBalance.boundaryCountPBalanced` and the
count along a chain `P10RoseEuler.chain_countP`).  It is true whenever the target is (drop the
closing equation from a witness of the target), so it is PLAUSIBLE exactly as the target
(module docstring of `P10RoseEndpoint/SingleRegion`: exhaustive search on small roses, not a
proof).  What remains is the planarity content: an extremal region of the flower meets each arc
in a prefix, a suffix or a whole arc, and the kept darts can be listed as a chain
`s₁ t₁⁻¹ s₂ t₂` with short sides.

## The lane residual with vertex-connectivity is not sufficient

The lane plan residual (a `Perm` of the kept filter plus vertex-connectivity of the kept darts,
closed by an Euler re-listing) does NOT imply the target: an Euler re-listing produces some closed
walk permuting the kept darts, but it need not have the block shape
`s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts` with the fixed blocks `s₁`, `s₂` of length at most
`eps` in the `Perm` clause, and connectivity says nothing about the order inside `s₁`, `s₂`.  The
chain clause is therefore kept in the residual.

## Imports

This module reaches the live chain (`P10Rose/Live/Reduction`, `Piece10Live/Cases`) through
`P10RoseEndpoint/SingleRegion`; it must not be imported together with the dead modules
(`P10Rose/SubArcMove`, `P10Rose/FilterMove`, `P10RoseKeptBalance/Kept`), whose declaration names
collide.  If the checker keeps `P10Rose/SubArcMove` instead, repointing the first import of
`P10RoseExtremal/Close` is enough: the names are identical.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

-- LOUD: REFUTED (lane gl-p10-48; Python model, not yet in Lean).
-- `RoseExtremalRegionStatement` is FALSE:
-- it implies `RoseExtremalJunctionStatement`, which fails on the gl-p10-40 G-face model with
-- the label-1 edges subdivided once (24 darts).  Corrected residual:
-- `P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement` (`JunctionCore.lean`).
/-- **An extremal-region witness for the rose step** (OPEN, PLAUSIBLE; the residual rose gap).
The target `P10Rose.RoseSingleRegionMoveStatement` with the closed-walk clause weakened to
"nonempty and chained"; the closing equation is supplied by `singleRegionMove_of_extremalRegion`. -/
def RoseExtremalRegionStatement : Prop :=
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
              (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts).IsChain
                (fun d e => X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
              s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi ∧
              t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

/-- **The single-region move from an extremal-region witness**: the chained re-listing of the kept
darts closes up, by balance. -/
theorem singleRegionMove_of_extremalRegion (h : RoseExtremalRegionStatement.{u, w, v}) :
    P10Rose.RoseSingleRegionMoveStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, hry, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hne, hchain,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, hrout, hry, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm,
    isClosedDartWalk_of_perm_filter K.boundary.cycle_nodup K.boundary.cycle_mem_iff
      (regionColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)
      (regionColour_indep K.boundary.cycle_mem_iff r) hperm hne hchain,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

/-- **The rose step from an extremal-region witness.** -/
theorem rose_of_extremalRegion (h : RoseExtremalRegionStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  P10Rose.rose_of_singleRegionMove (singleRegionMove_of_extremalRegion h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

/-- **The outer-pinch step from an extremal-region witness.** -/
theorem proof_of_extremalRegion (h : P10RoseExtremal.RoseExtremalRegionStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_singleRegionMove (P10RoseExtremal.singleRegionMove_of_extremalRegion h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal.RoseExtremalRegionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal.singleRegionMove_of_extremalRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal.rose_of_extremalRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_extremalRegion
