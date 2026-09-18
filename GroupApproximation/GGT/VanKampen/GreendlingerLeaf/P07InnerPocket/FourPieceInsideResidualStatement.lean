import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInsideCloseStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-48: the lake-only residual with local step clauses

## LOUD: the target `FourPieceInsideCloseResidualStatement` is NOT proved outright here

The target (`FourPieceInsideCloseStatement.lean`, lane gl-p07-45) asks, for every relator cell `C`
of the pocket that is off `a` and `b`, for a branch-1 witness `(faces, outerWalk)` or a branch-2
witness.  The obvious witness does not work:

* `faces := sideFaces K.walk` and `outerWalk := invDarts K.walk` form an enclosed face set when the
  complement cycle follows its boundary walk (`enclosedFaceSetSuccOfNoncrossing`).  But this fails
  clause 4.  A walk dart `d = α e` with `e` a dart of `K.walk` on the arc
  `invDarts (a.cellArcList i)` has `faceOf (α d) = faceOf e ∈ a.1`.  The side of `K` is the union of
  `a`, the pocket and `b` (`CellPocketWalk.exists_of_joinsCells`), so clause 4 fails at every dart
  of the walk that is not on a gap.
* `faces := {C.face}` passes clause 4 only when every edge of `C` lies on `K.walk`, on `∂a`, on
  `∂b` or across a gap.

So a branch-1 witness must be the pocket itself, `sideFaces K ∖ (a ∪ b)` or its component through
`C`, with lobes behind `G`-loops absorbed (lane gl-p07-26, model M12).  Its outside walk has to be
built from the planar structure.  That is the witness construction on which lanes gl-p07-46
(`AbsorbFaceSet`) and gl-p07-47 (`WitnessStepResidual`) work.  It is not attempted here.

## What this lane does: the meet of two existing reductions

Two reductions of the arc-audit residual `PocketFourPieceArcAuditResidualStatement` already exist:
* lane gl-p07-26 (`PocketFourPieceArcCloseStepStatement`) replaces the four arc clauses 4a, 4b
  (for `G₁/i` and `G₂/j`) by the local step clauses S1a, S1b.  All rotation, `invDarts` and
  arc-extraction work is proved in `FourPieceArcCloseArc.lean`;
* lane gl-p07-45 (`FourPieceInsideCloseResidualStatement`) asks for side inclusion only for lake
  walks, the witnesses whose outside walk reads no dart of `invDarts G₁` or `invDarts G₂`.

`FourPieceInsideResidualStepStatement` makes **both** changes.  Branch 1 keeps clauses 1, 2' and
the four no-interleave clauses.  Clause 3 is the lake-only side clause of lane 45.  Clauses 4a, 4b
are S1a, S1b of lane 26.
* **S1a.**  If some walk dart is off `G₁`, then at every position `p` where `ow[p]` and
  `ow[(p+1) % |ow|]` both lie on `G₁`, `facePerm ow[p]` is kept or `ow[p]` is pinch-free.
* **S1b.**  If every walk dart lies on `G₁`, at most one position is neither kept nor pinch-free.
* The same two clauses for `G₂/j`.

Endpoints (`FourPieceInsideResidualProof.lean`):
* `fourPieceInsideResidual_of_step`: the new statement gives
  `FourPieceInsideCloseResidualStatement`;
* `fourPieceInsideResidual_inside_of_step`: it gives `PocketFourPieceInsideStatement`;
* `fourPieceInsideResidual_step_of_arcCloseStep`: lane 26's gap gives the new statement.

## LOUD: strength

* **Strictly smaller in proof content than the target.**  A prover no longer extracts cyclic arcs
  from rotated `invDarts` blocks.  Only pointwise facts about single positions of the walk remain,
  exactly as in lane 26.
* **Weaker or equal as a `Prop` than lane 26's gap**: it is proved from it, since clause 3 only
  gains a hypothesis.  It is strictly smaller in proof content than lane 26's gap for the reason
  given by lane 45 (wedge model `{C, Π_j}`).
* Strictness as a `Prop` cannot be shown: all these statements are believed true, and true
  statements are equivalent as `Prop`s.

## Truth check

* Given `EnclosedFaceSetSucc`, S1a follows from clause 4a.  Apply 4a to the two-entry block of a
  consecutive `G₁` pair; the extracted arc makes `ow[p+1] = facePerm ow[p]`, which is kept.  S1b
  follows from clause 4b in the same way.  So the new statement holds whenever the target does.
* The lake-only clause is lane 45's.  Its wedge-model check applies unchanged: `{C, Π_i, Π_j}` is
  still excluded, `{C}` and `{C, Π_j}` are still witnesses.
* Lane 26's checks of S1a, S1b on M2, M5, M6, M7 and M12 with lobe-absorbing witnesses apply
  unchanged, because only clause 3 differs and it is weakened.

Truth status: that of the target, UNKNOWN / plausibly true (lanes 21c, 26, 28, 31, 45).
**Riskiest point:** unchanged, namely the construction of the pocket witness at pinch
pathologies, and the four no-interleave facts for it.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Residual of lane gl-p07-48.**  `FourPieceInsideCloseResidualStatement` with clauses 4a, 4b
replaced by the local step clauses S1a, S1b of `PocketFourPieceArcCloseStepStatement`.
Equivalently, `PocketFourPieceArcCloseStepStatement` with the lake-only side clause.  See the
module docstring. -/
def FourPieceInsideResidualStepStatement : Prop :=
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
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            ((∀ e ∈ invDarts X outerWalk,
                e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts) →
              faces ⊆ sideFaces X.toCombMap K.walk) ∧
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInsideResidualStepStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
