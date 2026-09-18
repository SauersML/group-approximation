import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseWalkStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-37c: the walk-degenerate residual with local step clauses

The target is `PinchCase.WalkDegenStatement` (`PinchCaseWalkStatement.lean`, lane gl-p07-34).
This file states the residual `PinchCase.WalkDegenStepStatement`; `WalkDegenStepProof.lean`
proves the target from it (`PinchCase.walkDegen_of_step`).  Certifies no printed sentence.

## The isolated statement

The premise block of `WalkDegenStatement`, verbatim, including the witness walk `outerWalk` of
`F = witnessFaces a b K C.face` and the two failure hypotheses.  In branch 1 of the conclusion,
clauses 4a/4b are replaced by the local step clauses S1a, S1b, S2a, S2b for the *new* walk, in
the form of `FourPieceWitness.NoPlanarDegenStepStatement` (lane gl-p07-33).  Branch 2 is
unchanged.  **Strictly smaller in proof content**: the rotation, `invDarts` and arc extraction of
4a/4b are proved (`ArcClose.exists_not_mem_of_block`, `arc_of_block`, `all_mem_of_invDarts`,
`arc_of_all`).

## LOUD: equivalent as a Prop, not strictly weaker

On an `EnclosedFaceSetSucc` walk, 4a gives S1a and 4b gives S1b (paper, as lane 26 notes).  For
4a: two cyclically consecutive entries `α ow[p+1], α ow[p]` are a prefix of a rotation of
`invDarts ow`, so they are `invDarts` of an arc `[ow[p], ow[p+1]]` of the cell (`arc_isChain_facePerm`).
Hence `ow[p+1] = facePerm ow[p]` and `facePerm ow[p]` is kept.  For 4b: the rotated walk is an arc,
so every position except the wrap is such a step.  Hence the residual holds exactly when
`WalkDegenStatement` does.

**Why no strictly weaker cut was found.**  A strictly weaker residual needs a consistent sub-case
of the premise block whose conclusion is proved.  The given walk never supplies branch 1 or
branch 2 with `faces = F`:
* the dart set of a bridge-free walk of `F` is fixed by `mem_iff`, and its order by `turn_next`;
* (3) with 4a and 4b would make it good, which `¬ good` excludes;
* branch 2 with it would need the whole walk on `G₁` with one junction, and then it is good.

So the cheap sub-cases are vacuous, and adding them as hypotheses would be an equivalent
restatement.  Every consistent sub-case needs a NEW face set with its enclosed walk, which is the
core planar content (absorb lakes, lobes and petals behind `G`-loops); the corpus lacks it.

## Truth check (paper)

Plausibly TRUE; no model refutes it.
* **M9** (a disc `a.1` in the middle of `G₁`).  (3) fails for the witness walk.  Branch 1 with
  `faces = sideFaces K.walk` (lane 31); the step clauses hold at the contiguous `G` blocks.
* **M11** (a lobe inside a third `G₁`-loop).  S1a fails at `λ_end`.  Branch 2 with `faces = {C}`.
* **P2 (new: two petals).**  The boundary of `Π_i` reads `A₁ X₁ A₂ X₂` inside `G₁`, with pinches
  `v` (start of `A₁`) and `w` (end of `A₁`).  `F` is bounded by `A₁ A₂`, so the walk lies on `G₁`
  with two junctions: S1b fails, while (3), S1a and S2 hold.  The complement of the closed face
  `Π_i` has three components, bounded by `A₁A₂`, `X₁` and `X₂`.  At most one of the `X`-petals `R₁`, `R₂`
  holds the exterior face.  If `R₁` does not, branch 2 holds with `faces = F ∪ R₁` (plus lakes):
  its walk `A₁ X₁ A₂` is one arc of `Π_i`.  Branch 2 carries no `⊆ sideFaces` clause, so `R₁`
  may contain `a`, `b` or `Π_j`.
* **Riskiest point** (unchanged from lanes 31 and 34): pinch pathologies where no single-arc
  enclosure of `C` exists and the lobe-absorbed witness still fails (3).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Remaining gap of lane gl-p07-37c.**  The premise block of `WalkDegenStatement`.  Then either
branch 1, with clauses 4a/4b replaced by the local step clauses S1a, S1b, S2a, S2b for the new
walk, or branch 2.  See the module docstring. -/
def WalkDegenStepStatement : Prop :=
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
        EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
          FourPieceWitness.witnessFaces a b K C.face) →
        ¬ (0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
            0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length ∧
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d)) →
