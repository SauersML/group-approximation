import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockWitnessLabel
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockCurve
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-32: step 2 of the nondegenerate four-block residual

Lane gl-p07-32.  The target is `FourPieceWitness.FourBlockNondegLabelStatement`
(`FourBlockWitnessLabel.lean`, lane gl-p07-27), from Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  This file states the residual `FourPieceWitness.WitnessCurveSublistNondegStatement`.
`FourBlockNondegStepProof.lean` proves the target, and `FourBlockNondegStatement`, from it.
Certifies no printed sentence on its own.

## Notation

* `F = witnessFaces a b K C.face` (`FourPieceWitnessDef.lean`), `l = invDarts X outerWalk`.
* `w = invDarts G₁ ++ sideAWord a b G₁ G₂ ++ cellG2Word G₁ G₂ ++ sideBWord b G₁ G₂`
  (`FourBlockCurve.lean`, lane gl-p07-22): the inverse pocket curve `Ḡ₁ · Ā · Ḡ₂ · B̄`, each entry
  kept only in the block of its priority class.

## Truth check of the target (on paper)

**TRUE; no counter-model found.  M11 does not refute it.**

*Two facts about the witness* (used in every model).
* (W1) An open face off the `Q₀`-class of `C` has no edge to a cut face: that edge is not a `∂P`
  edge, so the open face would lie in the same piece off `P`, hence be cut.  So the open faces
  off the class border only `Π_i`, `Π_j`, the outside, and class faces.
* (W2) A class face that borders a cut face `Q` does so across a `∂a` or `∂b` edge, so `Q ∈ a ∪ b`.

*Corner rule at a vertex `v`.*  Let the `F`-corners at `v` be `c₁, …, c_m` in rotation order.
`turn_next` sends the in-edge of `c_k` to the out-edge of `c_{k+1}`.  So a piece of `F` that meets
the rest of `F` only at `v` is inserted in the cyclic word between the edges of its two nearest
`F`-neighbours that face it.

*M11 (lane gl-p07-29; its candidate `a` has NONEMPTY arcs, main strip in `O`).*
`G₁ = μt' λ ν λ' μh'`, `C` is the `λ`-disc, `C'` lies in the `λ'`-disc, the `a`-lobe `A'` lies in
the `ν`-disc.
* If `C` is the `λ`-disc: the `O`-pocket `P₀` borders `a`, is off the class, so it is cut.  The
  `ν`-disc is cut.  `F = {C} ∪ λ'`-disc, the word is `λ λ'`, all `G1`: four blocks with
  `U₂ = U₃ = U₄ = []`.  (Clause 4b of the arc audit fails there; the four-block form does not.)
* If `C ∈ P₀`: the region between `μt'` and the path of `∂a` from `v` to `v₀` is cut, so
  `P₀` reads `μh' · B̄ · Ḡ₂ · Ā`, arriving at `v` along `Ā`.  The `F`-corners at `v` are `λ`, `λ'`,
  `P₀` in rotation order, so the word is `Ā λ λ' μh' B̄ Ḡ₂`.  The `G1` run `λ λ' μh'` is one cyclic
  interval: four blocks, and `λ λ' μh'` is in `Γ` order, so the residual below also holds.
* If `C` lies in the `ν`-disc next to the lobe: the `ν`-class has two corners at `v`, on both sides
  of the lobe corner.  The corner rule sends `ν_end` to `λ'_1` and `λ'_end` to `λ_1`, `λ_end` to
  `ν_1`, so `λ ν λ'` is one orbit and the lobe boundary is a second one.  No `EnclosedFaceSetSucc`
  walk exists (`mem_iff`); vacuous.

*M12 (a pinched `a`-lobe with nonempty arcs).*  The far side of `a` is pinched at `v` to a lobe
that runs along an edge segment `E` in the middle of `G₁ = G₁a · E · G₁b`.  The lobe cuts the
pocket into `P₁` (bounded by `G₁a`, the lobe and `∂a` from `v` to `v₀`) and `P₀` (the rest); they
touch only at `v`.  Either one borders `a`, so the one off the class of `C` is cut (W1).
`F = P₁` reads `G₁a · Ā`, and `F = P₀` reads `G₁b · B̄ · Ḡ₂ · Ā`: four blocks.  (This is the
figure-eight word `G₁b B G2 A [A G₁a A] A` that would refute the target if `P₀` and `P₁` were
both open.  They are not.)

*A `G1`-loop flanked by `A` and `B`.*  A loop `λ` of `Π_i` at `v` gives a two-sided failure only
if both its nearest `F`-neighbours at `v` face it across edges off `G₁`.  By (W1, W2) both flanks
then hold a cut region from `Π_i` to `a ∪ b`, and the nearest `F`-corner is the corner of the main
pocket between `B̄` and `Ā`.  That pocket then reads no `G₁` edge at `v`, and by the Jordan curve
`Ā(v → w) ∪ B̄(w → v)` the cell `Π_i` cannot reach a second such vertex `w`.  So the word is
`λ B̄ Ḡ₂ Ā`: four blocks.

*Degenerate models* M8, M9 are excluded by `0 < (a.cellArcList i).length`.

**So no pinch-bounded correction is needed.**  The M11 failure is a failure of the arc shape of
the `G1` block (clause 4b), not of the block order.

## The residual (`FourPieceWitness.WitnessCurveSublistNondegStatement`)

It keeps the premise block of `FourBlockNondegLabelStatement`, including the step 1 label.  Its
conclusion: some rotation `r` of `l` satisfies `r <+ w` or `r.reverse <+ w`.  This is the witness
version, for nondegenerate candidates, of `FourBlock.PocketCurveSublistStatement`
(`FourBlockStatement.lean`), which is stated for the lake fill of the pocket orbit instead.

*Truth.*  The walk of `F` follows the pocket curve `Γ`.  It skips the cyclic intervals of `Γ` that
bound cut regions, and it inserts the open loops of `Π_i` or `Π_j` at their pinch vertices, which
lie in `Γ` order (M11 above).  With all four arcs nonempty no dart of the walk is in two classes:
`α e` has one face, and `Π_i`, `Π_j` are not faces of `a` or `b`.  So the priority filter removes
nothing that the walk reads.  The reverse disjunct is a hedge for the orientation of `turn_next`.

## Why it is strictly smaller, and not a restatement

* **Not equivalent.**  The residual has a strictly stronger conclusion: it fixes the order inside
  every block, and it puts the `A` and `B` entries on the far sides.  The target asks for neither.
* **Strictly less proof content.**  Only the planar step "the witness walk follows `Γ`" is left.
  `FourBlockNondegStepProof.lean` proves the rest:
  - the priority bookkeeping (`FourBlock.mem_sideAWord`, `mem_cellG2Word`, `mem_sideBWord`);
  - the block split (`FourBlock.exists_blocks_of_sublist`);
  - the reverse reading (`FourBlock.exists_rotate_blocks_of_reverse_sublist`, `List.rotate_rotate`);
  - the step 1 label (`label_of_witness`, through `fourBlockNondeg_of_label`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-32: the witness outside walk follows the pocket curve, for
nondegenerate candidates.**  Some rotation of `invDarts X outerWalk`, or its reverse, is a sublist
of the priority-filtered inverse pocket curve `Ḡ₁ · Ā · Ḡ₂ · B̄`.  See the module docstring. -/
def WitnessCurveSublistNondegStatement : Prop :=
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
        ∃ n : ℕ,
          (invDarts X outerWalk).rotate n <+
              invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂ ++ FourBlock.cellG2Word G₁ G₂ ++
                FourBlock.sideBWord b G₁ G₂ ∨
            ((invDarts X outerWalk).rotate n).reverse <+
              invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂ ++ FourBlock.cellG2Word G₁ G₂ ++
                FourBlock.sideBWord b G₁ G₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessCurveSublistNondegStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
