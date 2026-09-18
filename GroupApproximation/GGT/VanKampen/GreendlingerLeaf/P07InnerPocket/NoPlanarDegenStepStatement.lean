import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceNoPlanarProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-33: the no-walk residual with local step clauses

## LOUD: truth check of `FourPieceWitness.NoPlanarDegenerateStatement` (lane gl-p07-28)

**Verdict: plausibly TRUE.**  No model refutes it; this is a paper check, not a formal proof.

Write `F = witnessFaces a b K C.face`.  The residual only speaks when `F` has no bridge-free
successor outside walk (hypothesis `hno`).
* **M2 (crescent, lane 21c).**  `F = {C}` has the witness walk `λ`, so `hno` fails.  Vacuous.
* **M9 (a degenerate `a` attached along `E` in the middle of `G₁`, lane 27).**  A witness walk
  exists, so the residual is vacuous.  M9 refutes `FourBlockStatement` and the noninterleave
  statement, not this one.
* **M11 (three `G₁`-loops at a pinch `v`, an `a`-lobe in the `ν`-disc, lane 29).**  A witness walk
  exists (`λ λ'`, or through `O`), so the residual is vacuous.  M11 refutes `ArcsAuditStatement` in
  case (i), not this one.
* **M8 (empty-arc island, lane 23).**  `F` is an annulus, so there is no walk.  Branch 1 holds with
  `faces = P' ∪ a.1`, and the walk reads `Ḡ₁ · B̄ · Ḡ₂` (lane 28).  The variant M8', where the
  island touches `G₁` at one vertex, behaves the same: that vertex pinches `a`, not `Π_i`.
* **M9 with a hole (a `b`-lobe cut off inside the pocket).**  There is no walk.  Branch 1 holds
  with the whole pocket, `faces = sideFaces K.walk`, as lane 31 reads M9.  The lake-filled witness alone fails clause 3.
* **M11 with a hole, `C` in the `O`-pocket.**  There is no walk.  Branch 1 holds with `faces = O ∪`
  the `λ`, `ν` and `λ'` discs `∪` the hole: absorbing the loops removes the jumps at `v`.

The mechanism in every case is the same: absorb the holes, lakes and lobes behind `G`-loops.
Absorbing is allowed when the exposed boundary lies on `G₁`/`G₂` edges.

## Why it is not proved here, and rejected cut-downs

Case (ii) needs a new face set (the witness with its lakes and lobes absorbed) together with its
boundary walk.  That is the core planar content, and the corpus does not have it.  These smaller
statements were checked and rejected:
* a fixed face set (the lake-filled witness) is FALSE (M9 with a hole fails clause 3);
* cell-intrinsic pinch-freeness in the conclusion is FALSE (M11 with a hole);
* restricting to nondegenerate contact arcs has no provable `_of_` (M8 is degenerate).

## The isolated statement (`FourPieceWitness.NoPlanarDegenStepStatement`)

It has the premise block of the residual, `hno`, and the extra hypothesis that (A) and (B) of
`witnessFaces_enclosedFaceSetSucc_of_connected` do not both hold.  The extra hypothesis is provable
(`not_connected_of_not_exists_walk`).  Its conclusion is that of
`PocketFourPieceArcCloseStepStatement` (lane 26): clause 4 is replaced by the local step clauses
S1a, S1b, S2a and S2b.

**Strictly smaller in proof content.**  The rotation, `invDarts` and arc-extraction work of
clauses 4a and 4b is proved (`ArcClose.exists_not_mem_of_block`, `ArcClose.arc_of_block`,
`ArcClose.all_mem_of_invDarts`, `ArcClose.arc_of_all`).  The connectivity failure is handed over as
a hypothesis.  Only pointwise facts about walk positions remain.

**True exactly when the residual is.**  Given `EnclosedFaceSetSucc`, S1a follows from 4a and S1b
from 4b (lane 26).  So the check above carries over.

**Endpoint.**  `FourPieceWitness.noPlanarDegenerate_of_step` (`NoPlanarDegenStepProof.lean`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Remaining gap of lane gl-p07-33.**  Under the premise block of
`NoPlanarDegenerateStatement`, with no witness walk and not both connectivity hypotheses,
branch 1 of `PocketFourPieceArcCloseStepStatement` (local step clauses) or branch 2 holds.  See the
module docstring. -/
def NoPlanarDegenStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    ∀ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i →
    ∀ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
      (¬ ∃ outerWalk : List X.toCombMap.Dart,
          EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk ∧
            ∀ d ∈ outerWalk,
              X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
      ¬ ((∀ f, f ∉ witnessFaces a b K C.face →
          f ∈ PocketNoncrossing.faceClass X.toCombMap
            (boundaryKeep X.toCombMap (witnessFaces a b K C.face)) X.outerFace) ∧
        (PocketOrbit.keepMap X.toCombMap (boundaryKeep X.toCombMap (witnessFaces a b K C.face))
          (boundaryKeep_alpha X.toCombMap (witnessFaces a b K C.face))).IsConnected) →
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            faces ⊆ sideFaces X.toCombMap K.walk ∧
            (∀ d ∈ outerWalk,
              X.toCombMap.alpha d ∈ invDarts X G₁.darts ∨
              X.toCombMap.alpha d ∈ invDarts X G₂.darts ∨
              (X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
                X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
                X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 ∧
                (walkKeep X.toCombMap K.walk (X.toCombMap.alpha d) ∨
                  walkKeep X.toCombMap a.2.boundary.cycle (X.toCombMap.alpha d) ∨
                  walkKeep X.toCombMap b.2.boundary.cycle (X.toCombMap.alpha d)))) ∧
            FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts)
              (invDarts X outerWalk) ∧
            FourPiece.CyclicNoInterleave
              (fun e => e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts)
              (invDarts X outerWalk) ∧
            FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
              (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i))
              (invDarts X outerWalk) ∧
            FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
              (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i))
              (invDarts X outerWalk) ∧
            ((∃ d ∈ outerWalk, d ∉ G₁.darts) →
              ∀ (p : ℕ) (hp : p < outerWalk.length), outerWalk[p] ∈ G₁.darts →
                outerWalk[(p + 1) % outerWalk.length]'(Nat.mod_lt _
                  (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ G₁.darts →
                walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) ∧
            ((∀ d ∈ outerWalk, d ∈ G₁.darts) →
              ∀ (p q : ℕ) (hp : p < outerWalk.length) (hq : q < outerWalk.length),
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[q]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q) ∧
            ((∃ d ∈ outerWalk, d ∉ G₂.darts) →
              ∀ (p : ℕ) (hp : p < outerWalk.length), outerWalk[p] ∈ G₂.darts →
                outerWalk[(p + 1) % outerWalk.length]'(Nat.mod_lt _
                  (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ G₂.darts →
                walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) ∧
            ((∀ d ∈ outerWalk, d ∈ G₂.darts) →
              ∀ (p q : ℕ) (hp : p < outerWalk.length) (hq : q < outerWalk.length),
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[q]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q)) ∨
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            ((∃ A : CyclicArc (cellDarts X i),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∨
              (∃ A : CyclicArc (cellDarts X j),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.NoPlanarDegenStepStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
