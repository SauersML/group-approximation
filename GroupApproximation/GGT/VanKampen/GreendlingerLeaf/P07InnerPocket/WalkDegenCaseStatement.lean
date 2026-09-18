import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenStepStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-39b: the walk-degenerate residual by cases and absorption

The target is `PinchCase.WalkDegenStepStatement` (`WalkDegenStepStatement.lean`, lane gl-p07-37c).
This file states the residual `PinchCase.WalkDegenCaseStatement`.  `WalkDegenCaseProof.lean`
proves the target from it (`PinchCase.walkDegenCase_step`) and the converse.  Certifies no printed
sentence.

## The case split

Write `F = witnessFaces a b K C.face` and `ow` for its witness walk.  The failure hypothesis
`hbad` says that the four noninterleave clauses (N) and the four step clauses S1a, S1b, S2a, S2b
do not all hold for `ow`.
* **Case N holds** (so a step clause fails; models M11, P2).  The witness pair `(F, ow)` is a
  *basic* pair in the sense of lane gl-p07-38 (`FourPieceWitness.AbsorbFaceSetBasic`).  This is
  proved outright (`walkDegenCase_witness_basic`, `WalkDegenCaseBase.lean`): `C.face ∈ F`
  (`mem_witnessFaces_self`), `F ⊆ sideFaces K.walk`, the dart clause (`dart_clause`, from the
  bridge-free hypothesis), and N.  So no Base is asked for in this case.
* **Case N fails** (model M9).  The residual asks for a basic pair or branch 2 (Base).  No step
  clause is required.
* **Both cases.**  The residual asks for lane 38's Improve step.  A basic pair whose step clauses
  fail comes with an exposed gap dart (`absorbFaceSet_exposed_of_basic`, proved).  It must be
  grown strictly, or made good, or branch 2 must hold.  Here Improve receives the whole
  walk-degenerate premise block, including the witness walk and `hbad`.

The iteration and its termination are lane 38's `absorbFaceSet_iterate`, reused.

## LOUD: equivalent as a Prop, strictly smaller in proof content

A good pair of the target serves as Base and as every Improve step, and branch 2 serves both.  So
the target implies the residual (`walkDegenCase_of_step`), and the two are **equivalent**
(`walkDegenCase_iff_step`).  No strictly weaker cut with a closed consistent case was found:
* every consistent case needs a NEW face set with its enclosed walk (37c's docstring shows that
  the witness walk alone never gives branch 1 or branch 2);
* the corpus has no construction of such a set (lake-fills of noncrossing walks need
  `FollowsBoundary` or the Q₀-orbit, and `sideFaces K.walk` fails the dart clause on nondegenerate
  contacts, `noWalkAbsorb_left_false`).
The proof content removed, compared with the target: Base on the consistent case N (M11, P2);
Base never needs the step clauses; the iteration, the termination, the exposed dart and the
reassembly of the thirteen clauses are all proved.

## Truth check (paper)

Plausibly TRUE: it is equivalent to the target, which no model refutes (37c's docstring).
* **M9.**  N fails.  Base: `sideFaces K.walk` with its walk (37c's reading), or the lobe-absorbed
  witness.
* **M11.**  N holds, S1a fails at `λ_end`.  Improve returns branch 2 with `faces = {C}`.
* **P2.**  N holds, S1b fails (two junctions).  Improve returns branch 2 with `faces = F ∪ R₁`.
* **Riskiest point** (unchanged from lanes 31, 34, 38): Improve when the lobe behind a `G₁`-loop
  is not inside the pocket (for example `Π_j` inside the loop).  There the `S F' ow'` disjunct or
  branch 2 must carry the step.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The four noninterleave clauses (N) for a walk**, verbatim from `WalkDegenStepStatement`. -/
abbrev WalkDegenCaseNoninterleave {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (b : RegionCandidate D eps X)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (outerWalk : List X.toCombMap.Dart) : Prop :=
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
      (invDarts X outerWalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.WalkDegenCaseNoninterleave
