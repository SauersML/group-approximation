import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOffStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-18: the lake reading, corrected

Lane gl-p07-18 targets `PocketFourPieceLakeReadStatement` (`FourPieceOffStatement.lean`), Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## LOUD: the target is FALSE, because of its last clause

The last clause says: if a contact arc on `Π_i` is empty and both arcs `A₁`, `A₂` are empty, then
some relator cell is not in `absorbed (sideFaces L) o`.  **That clause is false.**

*Model.*  `K = s₁ Ā₁ s₂ Ā₂`, where `Ā₁` is the **full** boundary of `Π_i` and `Ā₂` the full boundary
of `Π_j`.  Each cell hangs off the contour at one corner vertex (`v`, resp. `v'`), so it lies in
`sideOutside K` but meets the rest of `sideOutside K` only at that vertex.
* `b` is a strip of G-faces along `s₁`, and `a` a strip along `s₂`.  Both contact arcs are empty.
* The rest of the pocket is the single relator cell `C`.  Its boundary is: the far side of `b`,
  the loop around `Π_i`, the far side of `a`, the loop around `Π_j`.
* The only relator cells are `Π_i`, `Π_j` and `C`.
* Every hypothesis holds.  In particular both Euler equalities hold, since the outside of `K` is a
  wedge, and `G₁`, `G₂` are the full arcs.

*Why the clause fails.*
1. Any admissible `L` has `sideFaces L ⊆ sideFaces K \ (a ∪ b) = {C}`, so `sideFaces L = {C}`.
2. Every edge of `Π_i` borders `C`.  So `Π_i` cannot reach `o` across edges while avoiding `C`:
   it is absorbed.  The same holds for `Π_j`, and `C ∈ sideFaces L` is absorbed too.
3. An `Π_i`-dart `d` with `α d ∈ L` has face `Π_i ∉ component`, so it is not on the outer walk.
   The reading is therefore forced to have `A₁ = A₂ = 0`, and then the clause asks for a relator
   cell off the lake fill.  There is none.

The docstring argument "the connected outer side joins them to `o`" is wrong.  The outer side is
connected only through a vertex, and face components need shared edges.

`PocketFourPieceOffStatement` itself is not refuted by this model.  Its face set is existential,
and `{C}` is enclosed with `A₁`, `A₂` the full arcs, which makes its last clause vacuous.  **A
lake-filled face set can never give that clause.**

## Corrected statement

`PocketFourPieceLakeReadCoreStatement` is the target with the last clause removed.  The docstring
argument covers every clause kept: the clauses on `L`, "every outer walk is a rotation of one"
(proved in `LakeReadRotation.lean`), and the reading.  In the model, `L` is the reversed boundary
walk of `C`.  The outer walk reads the far side of `b`, then the far side of `a`, with
`A₁ = A₂ = 0`.

## The residual

`PocketFourPieceLakeReadSomeStatement` asks for the reading of **one** outer walk of the lake fill,
not every one.

**It is strictly smaller.**  `LakeReadEndpoint.lean` proves both directions.
* `lakeReadSome_of_core` builds the walk by `exists_lakeFill_of_noncrossing`, with
  `o ∉ sideFaces L` from the `L` clauses.
* `lakeReadCore_of_some` moves the reading to any other outer walk, by
  `EnclosedFaceSetSucc.eq_rotate_of_mem_iff` and a shift of `n`.

So the residual is equivalent to the corrected statement.  It drops the whole rotation-uniqueness
argument (part (a) of the lane), which the reduction proves.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent

/-- **Corrected lake reading: the target without its false degenerate off-cell clause.**  Every
outer walk of the lake fill of a chosen pocket walk `L` has the four-piece reading. -/
def PocketFourPieceLakeReadCoreStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        ∃ L : List X.toCombMap.Dart, IsNoncrossingClosedWalk X.toCombMap L ∧
          C.face ∈ sideFaces X.toCombMap L ∧
          (∀ f ∈ sideFaces X.toCombMap L, f ∈ sideFaces X.toCombMap K.walk ∧ f ∉ a.1 ∧
            f ∉ b.1 ∧ f ≠ (cell X i).face ∧ f ≠ (cell X j).face) ∧
          ∀ outerWalk : List X.toCombMap.Dart,
            EnclosedFaceSetSucc X (absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace)
              outerWalk →
            (∀ d : X.toCombMap.Dart, d ∈ outerWalk ↔ X.toCombMap.alpha d ∈ L ∧
              X.toCombMap.faceOf d ∈
                component X.toCombMap (sideFaces X.toCombMap L) X.outerFace) →
            ∃ (n : ℕ) (R₁ R₂ : List X.toCombMap.Dart) (A₁ : CyclicArc (cellDarts X i))
              (A₂ : CyclicArc (cellDarts X j)),
              invDarts X (outerWalk.rotate n) =
                  R₁ ++ invDarts X A₁.darts ++ R₂ ++ invDarts X A₂.darts ∧
                ((((∀ r ∈ R₁, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                      (∀ r ∈ R₁, X.toCombMap.alpha r ∈ b.sideFrom i)) ∧
                    ((∀ r ∈ R₂, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                      (∀ r ∈ R₂, X.toCombMap.alpha r ∈ b.sideFrom i))) ∨
                  ((∀ r ∈ R₁ ++ R₂,
                      X.toCombMap.alpha r ∈ a.sideFrom j ∨ X.toCombMap.alpha r ∈ b.sideFrom i) ∧
                    (A₁.length = 0 ∨ A₂.length = 0)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceLakeReadCoreStatement

/-- **Residual: the four-piece reading of one outer walk of the lake fill of a chosen pocket
walk `L`.**  It is equivalent to `PocketFourPieceLakeReadCoreStatement` and drops the
rotation-uniqueness argument.  See the module docstring. -/
def PocketFourPieceLakeReadSomeStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        ∃ L : List X.toCombMap.Dart, IsNoncrossingClosedWalk X.toCombMap L ∧
          C.face ∈ sideFaces X.toCombMap L ∧
          (∀ f ∈ sideFaces X.toCombMap L, f ∈ sideFaces X.toCombMap K.walk ∧ f ∉ a.1 ∧
            f ∉ b.1 ∧ f ≠ (cell X i).face ∧ f ≠ (cell X j).face) ∧
          ∃ outerWalk : List X.toCombMap.Dart,
            EnclosedFaceSetSucc X (absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace)
              outerWalk ∧
            (∀ d : X.toCombMap.Dart, d ∈ outerWalk ↔ X.toCombMap.alpha d ∈ L ∧
              X.toCombMap.faceOf d ∈
                component X.toCombMap (sideFaces X.toCombMap L) X.outerFace) ∧
            ∃ (n : ℕ) (R₁ R₂ : List X.toCombMap.Dart) (A₁ : CyclicArc (cellDarts X i))
              (A₂ : CyclicArc (cellDarts X j)),
              invDarts X (outerWalk.rotate n) =
                  R₁ ++ invDarts X A₁.darts ++ R₂ ++ invDarts X A₂.darts ∧
                ((((∀ r ∈ R₁, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                      (∀ r ∈ R₁, X.toCombMap.alpha r ∈ b.sideFrom i)) ∧
                    ((∀ r ∈ R₂, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                      (∀ r ∈ R₂, X.toCombMap.alpha r ∈ b.sideFrom i))) ∨
                  ((∀ r ∈ R₁ ++ R₂,
                      X.toCombMap.alpha r ∈ a.sideFrom j ∨ X.toCombMap.alpha r ∈ b.sideFrom i) ∧
                    (A₁.length = 0 ∨ A₂.length = 0)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceLakeReadSomeStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
