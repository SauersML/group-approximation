import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoPlanarDegenStepStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-35: the no-walk case with the whole pocket absorbed

Lane gl-p07-35.  The target is `FourPieceWitness.NoPlanarDegenStepStatement`
(`NoPlanarDegenStepStatement.lean`, lane gl-p07-33).  This file states the residual
`FourPieceWitness.NoWalkAbsorbStatement`.  `NoWalkAbsorbProof.lean` proves the target from it,
and the converse.  **LOUD: the two are equivalent, and the LEFT disjunct is dead** (LOUD 3).
Certifies no printed sentence on its own.

## LOUD 1: the suggested face set is a rejected candidate, so the whole pocket is used

The lane suggested the lake fill of the witness, i.e. the component of the complement of the
keep-map component containing `C.face`, together with `witnessFaces`.  With the face set fixed this
way, this is the REJECTED "fixed lake-filled witness", which is FALSE (M9 with a hole fails
clause 3).  The absorbed face set used here is the **whole pocket** `sideFaces X.toCombMap K.walk`.
It is explicit, it contains `C.face` (hypothesis `hCf`), and it is `⊆ sideFaces` by reflexivity.

## LOUD 2: equivalent as a Prop; strictly smaller only in proof content

The residual has the premise block of the target, and its conclusion is **LEFT ∨ (the target
conclusion)**.  So the target implies it (`noWalkAbsorb_of_noPlanarDegenStep`), and after the
reduction the two are **equivalent as Props**.  It is strictly smaller in proof content on the
LEFT route.  There the reduction proves:
* the face choice, `C.face ∈ faces` and `faces ⊆ sideFaces K.walk`;
* the `walkKeep K.walk` part of clause 2';
* **all four local step clauses S1a, S1b, S2a, S2b, in full.**

A LEFT-only statement is not given, because it may be false (see LOUD 3).

## LEFT

There is an outer walk `ow` of `P = sideFaces K.walk` such that:
* (walk) `EnclosedFaceSetSucc X P ow`;
* (bridge-free) every `d ∈ ow` has `faceOf (α d) ∈ P`;
* (darts) every `d ∈ ow` lies on `G₁` or `G₂`, or `faceOf (α d) ∉ a.1` and `faceOf (α d) ∉ b.1`;
* the four noninterleaving facts of clause 3, copied verbatim.

## How S1a/S1b follow (`NoWalkAbsorbLemmas.lean`)

* **Closure.**  Let `g ∈ G₁ ∩ ow` with `facePerm g ∈ G₁`.  Then `α (facePerm g)` is a dart of
  `invDarts K.firstArc ⊆ K.walk`, so its face is in `P` (`EqvGen.refl`).  Also
  `faceOf (facePerm g) = faceOf g ∉ P`.  So `facePerm g ∈ ow` by `mem_iff`.
* **S1a.**  If `facePerm ow[p] ∈ G₁`, closure gives `walkKeep`.  Otherwise `ow[p]` is the unique
  dart of `G₁` leaving `G₁` (`PocketRun.eq_of_facePerm_not_mem`).  Every other position of `G₁`
  steps to `facePerm` (`PocketRun.succ_eq_facePerm_of_keep`), and `ow[p+1] ∈ G₁`.  So by induction
  every walk dart lies on `G₁`, which contradicts the off-`G₁` hypothesis.
* **S1b.**  A position that is neither kept nor pinch-free has `facePerm` off `G₁` (closure).  By
  `eq_of_facePerm_not_mem` and `nodup` there is at most one such position.

## LOUD 3: truth check (corrected by lane gl-p07-35c)

The residual follows from the target, so it holds wherever the target holds.  It is
**equivalent** to the target (`noWalkAbsorb_iff_noPlanarDegenStep`, `NoWalkAbsorbProof.lean`).

**LEFT is FALSE on every nondegenerate instance.**  The whole pocket `sideFaces K.walk` contains
`a.1` and `b.1`, because `K.walk` runs along the contacts and near sides of `a` and `b`.  Its outer
walk therefore contains every contact dart `d ∈ a.cellArcList i` whose face (`Π_i`) is off the
pocket, and `faceOf (α d) ∈ a.1`.  So the dart clause fails unless `d ∈ G₁ ∪ G₂`
(`noWalkAbsorb_left_mem`, `noWalkAbsorb_left_false` in `NoWalkAbsorbAudit.lean`).  An earlier
draft of this docstring claimed LEFT in M9 and M11 with a hole.  That claim was wrong: both models
have nonempty contacts.  LEFT can hold only when the contacts and near sides of `a` and `b` are
empty or are bridges.  In every instance that matters, a proof of this statement has to prove the
right disjunct, which is the target conclusion.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-35.**  Under the premise block of `NoPlanarDegenStepStatement`,
either the whole pocket `sideFaces K.walk` has a bridge-free successor outer walk whose darts
off `G₁`/`G₂` have no `a` or `b` face across and which satisfies clause 3, or the target
conclusion holds.  See the module docstring. -/
def NoWalkAbsorbStatement : Prop :=
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
        (∃ outerWalk : List X.toCombMap.Dart,
          EnclosedFaceSetSucc X (sideFaces X.toCombMap K.walk) outerWalk ∧
            (∀ d ∈ outerWalk,
              X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk) ∧
            (∀ d ∈ outerWalk, d ∈ G₁.darts ∨ d ∈ G₂.darts ∨
              (X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
                X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1)) ∧
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
              (invDarts X outerWalk)) ∨
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.NoWalkAbsorbStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
