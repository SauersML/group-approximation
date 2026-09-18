import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceNoPlanarStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-33: the corrected consumer's one gap (pinched reading)

## LOUD: the existing consumers each take a FALSE input

`FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_noninterleave_arcsAudit` takes
`ArcsAuditStatement`, which is FALSE (M11, lane 29).  Its noninterleave input is also FALSE (M9,
lane 27).  The `_fourBlock_` variant takes `FourBlockStatement`, which is FALSE (M9).  So neither
consumer proves anything.

## Pinch-freeness cannot be supplied from the hypotheses

The premise block of `PocketFourPieceArcAuditResidualStatement` allows pinched cells:
* in M2 (lane 21c) the last dart `x` of `λ ⊆ G₁` is not `PocketRun.PinchFreeAt`;
* in M11 the darts `λ_end`, `ν_end` and `λ'_end` are not.

The proved `FourPieceWitness.ArcsAuditPinchStatement` needs, for `G₁` (and the same for `G₂`):
* **(good-a)** every dart of `G₁` is pinch-free, whenever the walk has an off-`G₁` entry (clause
  4a);
* **(good-b)** at most one dart of `G₁` is pinched, whenever the walk is all `G₁` (clause 4b).

These pinch bounds are isolated as the one gap.  Clause 3 (the four noninterleaving facts) has no
true unconditional form either (M9), so it goes into the same gap.

## The gap (`FourPieceWitness.NoPlanarDegenPinchReadStatement`)

It has the premise block of the residual.  For every bridge-free successor outside walk of
`witnessFaces a b K C.face`:
* **either** the four noninterleaving facts and (good-a)/(good-b) for `G₁` and `G₂` hold,
* **or** the target conclusion (branch 1 or branch 2) holds.

**Strictly weaker than the target.**  The target gives the right disjunct
(`FourPieceWitness.pinchRead_of_arcAuditResidual`).  Where the left disjunct holds, the gap asks for
nothing about arcs: `C.face ∈ F`, `F ⊆ sideFaces`, clause 2' and clause 4 are all proved.  They
come from `mem_witnessFaces_self`, `witnessFaces_subset_sideFaces`, `dart_clause` and the proved
`arcsAuditPinch`.

**Truth check (on paper).**  The gap follows from the target, so it holds wherever the target does.
Model by model:
* **M2.**  The walk `λ` is all `G₁`.  (good-a) for `G₁` is vacuous, and (good-b) holds because only
  `x` is pinched.  The noninterleaving facts are trivial.  If `Π_j` is pinched, the right
  disjunct holds through branch 1 of lane 21c.
* **M9.**  A walk exists and noninterleaving fails, so the right disjunct holds: branch 1 with
  `faces = sideFaces K.walk` (lane 31).
* **M11.**  (good-a)/(good-b) fail for `G₁`, so the right disjunct holds: branch 2 with
  `faces = {C}`, the `λ`-disc.
* **M8.**  There is no witness walk, so the gap is vacuous.

**Endpoints** (`NoPlanarDegenPinchProof.lean`):
* `FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_pinch (hdeg) (hpinch) (hread)`;
* `FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_pinchRead (hdeg) (hread)`, which
  discharges `hpinch` with `arcsAuditPinch`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **The one gap of the corrected consumer (lane gl-p07-33).**  For every witness walk, either the
four noninterleaving facts and the pinch bounds for `G₁` and `G₂` hold, or the target conclusion
holds.  See the module docstring. -/
def NoPlanarDegenPinchReadStatement : Prop :=
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
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
        (FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts)
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
          ((∃ e ∈ invDarts X outerWalk, e ∉ invDarts X G₁.darts) →
            ∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
          ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts) →
            ∀ d ∈ G₁.darts, ∀ d' ∈ G₁.darts, ¬ PocketRun.PinchFreeAt X.toCombMap d →
              ¬ PocketRun.PinchFreeAt X.toCombMap d' → d = d') ∧
          ((∃ e ∈ invDarts X outerWalk, e ∉ invDarts X G₂.darts) →
            ∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
          ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₂.darts) →
            ∀ d ∈ G₂.darts, ∀ d' ∈ G₂.darts, ¬ PocketRun.PinchFreeAt X.toCombMap d →
              ¬ PocketRun.PinchFreeAt X.toCombMap d' → d = d')) ∨
        ((∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
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
            (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
              (invDarts X outerWalk).rotate m = U ++ V →
              (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
              (∃ e ∈ V, e ∉ invDarts X G₁.darts) →
              ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
            ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts) →
              ∃ (n : ℕ) (A : CyclicArc (cellDarts X i)),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∧
            (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
              (invDarts X outerWalk).rotate m = U ++ V →
              (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
              (∃ e ∈ V, e ∉ invDarts X G₂.darts) →
              ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts) ∧
            ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₂.darts) →
              ∃ (n : ℕ) (A : CyclicArc (cellDarts X j)),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts)) ∨
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            ((∃ A : CyclicArc (cellDarts X i),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∨
              (∃ A : CyclicArc (cellDarts X j),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.NoPlanarDegenPinchReadStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
