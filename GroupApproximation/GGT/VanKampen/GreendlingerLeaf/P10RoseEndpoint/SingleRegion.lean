import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.Cases
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose endpoint chain, part 1: the sub-arc region move from a single-region move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-04 (a).  This module is a copy of `P10Rose/SubArcMove`
(declarations and proofs verbatim) that imports the live chain `P10Rose/Live/Reduction` instead of
the dead filter route (`P10Rose/SubArc`, `P10Rose/Proof`, `P10Rose/InPlaceFilter`,
`P10Rose/FilterWalk`, `P10Rose/FilterMove`).  The declaration names collide intentionally with
`P10Rose/SubArcMove`; the two modules must never be imported together.

* `SubArcMove.regionColour` and its API: the colouring `true` exactly on the face class of a dart
  `r` for `FaceClassStep M (walkKeep M c)`; it is region-constant (`regionColour_step`), never
  colours both sides of a cycle dart (`regionColour_indep`), and removes every cycle dart with a
  side in the class (`movePred_regionColour_eq_false`).
* `RoseSingleRegionMoveStatement` (OPEN, the innermost remaining rose gap).
* `regionMoveSubArc_of_singleRegionMove`, `rose_of_singleRegionMove`: its reductions to
  `RoseRegionMoveSubArcStatement` (`P10Rose/Live/Reduction`) and `P10ChordLift.RoseStepStatement`.
* `Piece10.proof_of_regionMoveSubArc`, `Piece10.proof_of_singleRegionMove`: the outer-pinch step
  `PocketOuterPinchStepSectionStatement` from either gap, through `Piece10.proof_of_rose`
  (`Piece10Live/Cases`; the non-rose case is closed there by `P10ChordLift.proof`).

## Why `RoseSingleRegionMoveStatement` is expected to be true (PLAUSIBLE, not certain)

The edges of the cycle form a plane Eulerian graph whose faces are the regions, two-coloured by the
face set; a one-region move deletes the facial walk of one region `R` other than the exterior one,
so the kept darts stay balanced at every vertex and the `Perm` clause lets them be re-listed as a
closed walk.  On the three-petal flower the move flips the single region `{p₂, q₂}`.  A search over
every rose configuration with at most five walk darts and about a hundred random ones with six to
twelve darts found a one-region move each time.  Not a proof: the planarity argument (an extremal
region meets the arcs only in a prefix, a suffix or a whole arc, and its removal leaves short sides)
is not formalised.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides FilterMove

namespace SubArcMove

/-- **The colouring of one region**: `true` exactly on the face-class of `r`. -/
noncomputable def regionColour (M : CombMap.{v}) (keep : M.Dart → Prop) (r x : M.Dart) : Bool :=
  @ite Bool (Relation.EqvGen (CombMap.FaceClassStep M keep) r x) (Classical.propDecidable _)
    true false

theorem regionColour_eq_true_iff (M : CombMap.{v}) (keep : M.Dart → Prop) (r x : M.Dart) :
    regionColour M keep r x = true ↔ Relation.EqvGen (CombMap.FaceClassStep M keep) r x := by
  unfold regionColour
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

/-- Two Booleans with the same truth are equal. -/
theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd (h.mpr rfl) (by decide)
  · exact absurd (h.mp rfl) (by decide)
  · rfl

/-- The colouring of one region is constant along the face-class steps. -/
theorem regionColour_step (M : CombMap.{v}) (keep : M.Dart → Prop) (r : M.Dart) :
    ∀ x y, CombMap.FaceClassStep M keep x y →
      regionColour M keep r x = regionColour M keep r y := by
  intro x y hxy
  apply bool_eq_of_iff
  rw [regionColour_eq_true_iff, regionColour_eq_true_iff]
  exact ⟨fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ hxy),
    fun h => Relation.EqvGen.trans _ _ _ h
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hxy))⟩

/-- A dart outside the class of `r` is not flipped. -/
theorem regionColour_eq_false (M : CombMap.{v}) (keep : M.Dart → Prop) {r x : M.Dart}
    (hx : ¬Relation.EqvGen (CombMap.FaceClassStep M keep) r x) :
    regionColour M keep r x = false := by
  cases h : regionColour M keep r x with
  | false => rfl
  | true => exact absurd ((regionColour_eq_true_iff M keep r x).mp h) hx

/-- One region never contains both sides of a dart of the boundary cycle. -/
theorem regionColour_indep {M : CombMap.{v}} {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) (r : M.Dart) :
    ∀ d ∈ c, regionColour M (walkKeep M c) r d = false ∨
      regionColour M (walkKeep M c) r (M.alpha d) = false := by
  intro d hd
  cases h1 : regionColour M (walkKeep M c) r d with
  | false => exact Or.inl rfl
  | true =>
    cases h2 : regionColour M (walkKeep M c) r (M.alpha d) with
    | false => exact Or.inr rfl
    | true =>
      exfalso
      have e1 := (regionColour_eq_true_iff M (walkKeep M c) r d).mp h1
      have e2 := (regionColour_eq_true_iff M (walkKeep M c) r (M.alpha d)).mp h2
      obtain ⟨hin, hout⟩ := (hc d).mp hd
      exact hout ((faceOf_mem_iff_of_walkEqvGen hc
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ e1) e2)).mp hin)

/-- A dart with a side in the class of `r` is removed by the move. -/
theorem movePred_regionColour_eq_false {M : CombMap.{v}} {c : List M.Dart} {r y : M.Dart}
    (hy : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r y ∨
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r (M.alpha y)) :
    movePred M (regionColour M (walkKeep M c) r) y = false := by
  cases hp : movePred M (regionColour M (walkKeep M c) r) y with
  | false => rfl
  | true =>
    obtain ⟨h1, h2⟩ := (movePred_eq_true_iff M _ y).mp hp
    rcases hy with hy | hy
    · exact absurd ((regionColour_eq_true_iff M _ r y).mpr hy) (by rw [h1]; decide)
    · exact absurd ((regionColour_eq_true_iff M _ _ _).mpr hy) (by rw [h2]; decide)

end SubArcMove
open SubArcMove

-- LOUD: REFUTED (lane gl-p10-48; Python model, not yet in Lean).
-- `RoseSingleRegionMoveStatement` is FALSE:
-- it implies `RoseExtremalJunctionStatement`, which fails on the gl-p10-40 G-face model with
-- the label-1 edges subdivided once (24 darts).  Corrected residual:
-- `P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement` (`JunctionCore.lean`).
/-- **A single-region move for the rose step** (OPEN; the innermost remaining rose gap).  Under the
rose hypotheses, some dart `r` whose region avoids the exterior face and meets a side of a dart of
the cycle gives, with `z = regionColour r`, the listing clauses of `RoseRegionMoveSubArcStatement`.
See the module docstring for the evidence. -/
def RoseSingleRegionMoveStatement : Prop :=
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
              IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
              s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi ∧
              t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

/-- **The sub-arc region move from a single-region move**: flip the region of `r`. -/
theorem regionMoveSubArc_of_singleRegionMove (h : RoseSingleRegionMoveStatement.{u, w, v}) :
    RoseRegionMoveSubArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, ⟨y, hy, hry⟩, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hwalk,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hz := regionColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r
  exact ⟨regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r, hz,
    regionColour_indep K.boundary.cycle_mem_iff r,
    not_mem_flipFaces hz K.outerFace_not_mem
      (fun x hx => regionColour_eq_false X.toCombMap _ (hrout x hx)),
    ⟨y, hy, movePred_regionColour_eq_false hry⟩, source, kept, hsource, hkept, t₁, t₂, s₁, s₂,
    hperm, hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

/-- **The rose step from a single-region move.** -/
theorem rose_of_singleRegionMove (h : RoseSingleRegionMoveStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  rose_of_regionMoveSubArc (regionMoveSubArc_of_singleRegionMove h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

/-- **The outer-pinch step from the sub-arc region move.** -/
theorem proof_of_regionMoveSubArc (h : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_rose (P10Rose.rose_of_regionMoveSubArc h)

/-- **The outer-pinch step from a single-region move.** -/
theorem proof_of_singleRegionMove (h : P10Rose.RoseSingleRegionMoveStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_rose (P10Rose.rose_of_singleRegionMove h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour_eq_true_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.bool_eq_of_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour_eq_false
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour_indep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.movePred_regionColour_eq_false
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseSingleRegionMoveStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.regionMoveSubArc_of_singleRegionMove
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.rose_of_singleRegionMove
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_regionMoveSubArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_singleRegionMove
