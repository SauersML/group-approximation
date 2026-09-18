import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinAt
import GroupApproximation.Meta.AxiomGuard

/-!
# Pointwise conclusions of the rose lobe chain, part 2

Lane gl-p10-74.  Continues `P10RoseLobe/OsinAt`: for a fixed pocket `K`,
`roseLobeOsin_FilterAt K`, `roseLobeOsin_LobeAt K`, `roseLobeOsin_SubArcAt K` and
`roseLobeOsin_InPlaceAt K` are the conclusions, verbatim, of `roseLobe_FilterListingStatement`,
`P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement`,
`P10Rose.RoseRegionMoveSubArcStatement` and `P10Rose.RoseInPlaceStepStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The conclusion of `roseLobe_FilterListingStatement` at the pocket `K`. -/
abbrev roseLobeOsin_FilterAt (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ rs : List X.toCombMap.Dart,
    ((rs ≠ [] ∧ ∀ r ∈ rs, r ∈ K.boundary.cycle) ∨
      ∃ r, rs = [r] ∧
        (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
        ∃ y ∈ K.boundary.cycle, Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
          Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
    (cell X K.source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
      X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
    (cell X K.kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
      X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
    (∃ t₁ : CyclicArc (cellDarts X K.source),
      (invDarts X K.sourceArc.darts).filter (movePred X.toCombMap
        (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
          rs)) = invDarts X t₁.darts) ∧
    (∃ t₂ : CyclicArc (outerDarts X),
      K.targetArc.darts.filter (movePred X.toCombMap
        (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
          rs)) = t₂.darts ∧
      K.targetArc.start.1 ≤ t₂.start.1 ∧
      t₂.start.1 + t₂.length ≤ K.targetArc.start.1 + K.targetArc.length) ∧
    IsClosedDartWalk X.toCombMap (K.boundary.cycle.filter (movePred X.toCombMap
      (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_FilterAt

/-- The conclusion of `P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement` at `K`. -/
abbrev roseLobeOsin_LobeAt (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ rs : List X.toCombMap.Dart,
    ((rs ≠ [] ∧ ∀ r ∈ rs, r ∈ K.boundary.cycle) ∨
      ∃ r, rs = [r] ∧
        (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
        ∃ y ∈ K.boundary.cycle, Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
          Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
    ∃ (source kept : Fin X.rCellCount),
      (cell X source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
      (cell X kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
      ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
        (s₁ s₂ : List X.toCombMap.Dart),
        List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
          (K.boundary.cycle.filter (movePred X.toCombMap (roseJunctionCore_lobeColour
            X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs))) ∧
        IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
        s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
        t₂.start.1 + t₂.length ≤ hi ∧
        t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_LobeAt

/-- The conclusion of `P10Rose.RoseRegionMoveSubArcStatement` at `K`. -/
abbrev roseLobeOsin_SubArcAt (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ z : X.toCombMap.Dart → Bool,
    (∀ x y, CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y) ∧
    (∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false) ∧
    X.outerFace ∉ flipFaces X.toCombMap K.faces z ∧
    (∃ y ∈ K.boundary.cycle, movePred X.toCombMap z y = false) ∧
    ∃ (source kept : Fin X.rCellCount),
      (cell X source).face ∉ flipFaces X.toCombMap K.faces z ∧
      (cell X kept).face ∈ flipFaces X.toCombMap K.faces z ∧
      ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
        (s₁ s₂ : List X.toCombMap.Dart),
        List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
          (K.boundary.cycle.filter (movePred X.toCombMap z)) ∧
        IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
        s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
        t₂.start.1 + t₂.length ≤ hi ∧
        t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_SubArcAt

/-- The conclusion of `P10Rose.RoseInPlaceStepStatement` at `K`. -/
abbrev roseLobeOsin_InPlaceAt (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
    K'.sourceArc.length < (cellDarts X K'.source).length ∧
    K'.targetArc.length < (outerDarts X).length ∧
    K'.repeatedVisits < K.repeatedVisits

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_InPlaceAt

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
