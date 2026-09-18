import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockNondegStepStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-36c: the local step residual of the witness curve sublist

Lane gl-p07-36c.  The target is `FourPieceWitness.WitnessCurveSublistNondegStatement`
(`FourBlockNondegStepStatement.lean`, lane gl-p07-32), from Osin, arXiv:math/0411039v3, §9, proof
of Lemma 9.7(b).  This file states the residual `FourPieceWitness.WitnessCurveSublistStepStatement`.
`WitnessCurveSublistProof.lean` proves the target from it
(`FourPieceWitness.witnessCurveSublistNondeg_of_step`).  Certifies no printed sentence on its own.

## Notation

* `l = invDarts X outerWalk`, the inverse outside walk of the witness face set.
* `w = witnessSublistCurve a b G₁ G₂ = invDarts G₁ ++ sideAWord ++ cellG2Word ++ sideBWord`,
  the priority-filtered inverse pocket curve (`FourBlockCurve.lean`).  It is definitionally the
  word in the conclusion of the target.
* `StepNext w l x y` (`WitnessCurveSublistList.lean`): `x` comes before `y` in `w`, or `y` is the
  first entry of `w` that lies in `l`.

## The residual

Same premise block as the target.  Conclusion: every consecutive pair `(x, y)` of every rotation
of `l` is a `StepNext w l x y` pair, or every such pair read backwards is a `StepNext w l y x`
pair.  This is the local form of "the walk follows the curve": each step of the witness walk
moves forward along `Γ`, except the one step that wraps around to the first entry of `Γ`.

## Truth check (on paper)

**TRUE, provided the target is true.  Lane gl-p07-32 checked the target on the models M11 and M12
and in the degenerate cases, and found no counter-model.**  If `r = l.rotate n <+ w`, then the
elements of `r` appear in `w` in the order of `r`, and `l` has the same elements as `r`.  So the
head of `r` is the first entry of `w` in `l`.  A consecutive pair of a rotation of the
duplicate-free `l` is either consecutive in `r`, which is a forward step, or it is (last of `r`,
head of `r`), which is the second disjunct of `StepNext`.  The case `r.reverse <+ w` is the same
argument applied to `l.reverse`, and gives the backward disjunct.

## LOUD: equal in logical strength, strictly smaller in proof content

**This residual is logically EQUIVALENT to the target, given facts that are proved here.**  The
converse argument just above uses only that `w` and `l` are duplicate free and that `l ⊆ w`, and
`WitnessCurveSublistProof.lean` proves all three from the premises.  So the residual is **not**
strictly weaker in logical strength.

It is **strictly smaller in proof content**.  `WitnessCurveSublistRotate.lean` and
`WitnessCurveSublistProof.lean` prove the following parts, and none of them is left:
* the global chaining from local steps to a sublist, via `exists_first_entry`,
  `first_entry_unique`, `sublist_of_forward` and `exists_rotate_sublist_of_steps`;
* the choice of the rotation that starts at the first entry of `w` in `l`, together with the
  proof that no step of that rotation wraps around;
* the orientation bookkeeping of the reverse disjunct (`exists_rotate_reverse_sublist_of_steps`,
  `List.rotate_reverse`);
* `w` duplicate free.  Each block is duplicate free, and the priority filter makes the four
  blocks pairwise disjoint (`witnessSublist_curve_nodup`);
* `l` duplicate free (`EnclosedFaceSet.nodup`), and `l ⊆ w` from the step 1 label `hlab`
  (`witnessSublist_mem_curve`).

What is left is one planar fact about a single step: each turn `x ↦ y` of the witness walk moves
forward along `Γ`, or wraps around to the first entry of `Γ`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section Curve

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The priority-filtered inverse pocket curve** `Ḡ₁ · Ā · Ḡ₂ · B̄`.  It is the word in
the conclusion of `WitnessCurveSublistNondegStatement`. -/
noncomputable def witnessSublistCurve (a b : RegionCandidate D eps X)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) : List X.toCombMap.Dart :=
  invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂ ++ FourBlock.cellG2Word G₁ G₂ ++
    FourBlock.sideBWord b G₁ G₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessSublistCurve

end Curve

/-- **Residual of lane gl-p07-36c: every step of the witness outside walk is a forward step of
the pocket curve, except the step that wraps around to its first entry.**  Same premises as
`WitnessCurveSublistNondegStatement`.  LOUD: this is logically equivalent to that target, given
the proved nodup and membership facts.  It is strictly smaller only in proof content.  See the
module docstring. -/
def WitnessCurveSublistStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    0 < (a.cellArcList i).length → 0 < (a.cellArcList j).length →
    0 < (b.cellArcList i).length → 0 < (b.cellArcList j).length →
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
        (∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
          X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i) →
        (∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) x y) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessCurveSublistStepStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
