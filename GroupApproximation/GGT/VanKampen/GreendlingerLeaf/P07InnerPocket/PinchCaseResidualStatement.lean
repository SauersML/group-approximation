import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseRestStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-34: the good-walk cut of clause (rest)

The target is `PinchCase.RestStatement` (`PinchCaseRestStatement.lean`), the second clause of
`SoundRoute.PinchCaseStatement`: the arc-audit residual in the degenerate-arc and pinched cases.

## What is proved: the good-walk case

Write `F = witnessFaces a b K C.face`.  A *witness walk* is `ow` with
`EnclosedFaceSetSucc X F ow` and `faceOf (α d) ∈ F` for `d ∈ ow`.  Call it *good* when
* **(3)** the four noninterleaving facts hold for `invDarts X ow`, and
* **(S)** the local step clauses of lane gl-p07-26 hold (the shape of
  `FourPieceWitness.NoPlanarDegenStepStatement`):
  - S1a: if `ow` has a dart off `G₁`, then at every position `p` where `ow[p]` and its successor
    lie on `G₁`, `facePerm ow[p]` is kept by `ow` or `ow[p]` is `PocketRun.PinchFreeAt`;
  - S1b: if every dart of `ow` lies on `G₁`, at most one position is neither kept nor pinch-free;
  - S2a, S2b: the same for `G₂`.

If a good walk exists, branch 1 of the conclusion holds with `faces = F`
(`PinchCase.rest_of_residual`, `PinchCaseProof.lean`): clause 1 by `mem_witnessFaces_self` and
`witnessFaces_subset_sideFaces`, clause 2' by `dart_clause`, clause 3 by (3), clause 4a by
`ArcClose.arc_of_block` and clause 4b by `ArcClose.arc_of_all`.  **Neither nondegenerate contact
arcs nor global pinch-freeness is used.**  So every degenerate-arc or pinched configuration that
has a good witness walk is closed here.

## The residual (`PinchCase.ResidualStatement`)

The premise block, `¬ case (i)`, and **no good witness walk**, give the conclusion.

**LOUD: logical strength.**  `ResidualStatement` and `RestStatement` are logically *equivalent*:
`rest_of_residual` and `residual_of_rest` are both proved.  Every sound cut whose removed case is
proved has this property.  The residual is strictly smaller in proof content: it asserts nothing
where a good walk exists (models T2 and M2 below), where `RestStatement` asserts branch 1.

**Split** (`PinchCase.residual_of_noPlanarDegenerate_walkDegen`): the residual follows from lane
28's `FourPieceWitness.NoPlanarDegenerateStatement` (no witness walk at all; sibling gl-p07-33
reduces it to `NoPlanarDegenStepStatement`) together with `PinchCase.WalkDegenStatement`
(`PinchCaseWalkStatement.lean`): a witness walk exists, case (i) fails, and the walk is not good.

## Truth check (paper, small van Kampen configurations)

* **T1 (square).**  `Π_i`, `Π_j`, strips `a` and `b` along edges, one relator cell `C` in the
  pocket.  Arcs nonempty, pinch-free, a witness walk exists: case (i).  Rest and residual vacuous.
* **T2 (vertex contact).**  As T1, but `a` meets `Π_i` at one vertex, so `a.cellArcList i = []`
  and case (i) fails.  The walk reads `Ḡ₁ · B̄ · Ḡ₂ · Ā`, a four-block word, so (3) holds.
  `Π_i` and `Π_j` visit every vertex once, so every `G`-dart is pinch-free; S1a/S2a hold, S1b/S2b
  are vacuous.  Good walk: **closed by the proved case**; the residual is vacuous.
* **M2 (crescent, lane 21c).**  Only `x`, the last dart of the loop `λ ⊆ G₁`, is pinched, so case
  (i) fails.  The walk `λ` lies on `G₁`: the four predicates are constant on it, so (3) is
  trivial; S1b holds with the single junction `x`; S2a/S2b are vacuous.  Good walk: **closed**.
* **M8 (empty-arc island, lane 23).**  No witness walk.  The residual asserts; branch 1 holds with
  `faces = P' ∪ a.1`, the walk reading `Ḡ₁ · B̄ · Ḡ₂` (lane 28).
* **M9 (a disc `a.1` in the middle of `G₁`, lane 27).**  A walk exists but (3) fails for it (and
  for its rotations, since `CyclicNoInterleave` is rotation invariant).  The residual asserts;
  branch 1 holds with `faces = sideFaces K.walk` (lane 31).
* **M11 (a lobe inside a third `G₁`-loop, lane 29).**  S1a fails at `λ_end`: `facePerm λ_end = ν₁`
  is not kept and `λ_end` is pinched.  The residual asserts; branch 2 holds with `faces = {C}`.

No model refutes the residual.  Its truth is inherited from `RestStatement` (plausibly true,
unproved).  **Riskiest point** (unchanged from lane 31): pinch pathologies where `C` is not
enclosed by a single loop of `Π_i`, so branch 2 is unavailable, and the lake-filled witness is
not good.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Residual of lane gl-p07-34.**  Clause (rest) of `SoundRoute.PinchCaseStatement` with the
extra hypothesis that `witnessFaces a b K C.face` has no *good* witness walk (four noninterleaving
facts plus the local step clauses).  See the module docstring. -/
def ResidualStatement : Prop :=
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
        ¬ (0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
            0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length ∧
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            ∃ outerWalk : List X.toCombMap.Dart,
              EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
                ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
                  FourPieceWitness.witnessFaces a b K C.face) →
        (¬ ∃ outerWalk : List X.toCombMap.Dart,
            EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
            (∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
              FourPieceWitness.witnessFaces a b K C.face) ∧
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
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q)) →
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
                  invDarts X (outerWalk.rotate n) = invDarts X A.darts)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.ResidualStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
