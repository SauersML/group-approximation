import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBoundPocket
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket assembly: the remaining four-piece reading

Lane gl-p07-15.  The target is `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`InnerTwoArcLong.lean:55`), Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).
`Assembly.lean` reduces it to the single residual `PocketFourPieceOffStatement` below.  The
reduction proves the ε-bounds (lane 11), the off cells of nonempty arcs (`AssemblyCellOff.lean`),
and the normal form (lanes 13 and 14).

## The residual

Under the hypotheses of the target, the statement asks for:
* an enclosed face set `faces ∋ C` with successor turns;
* a rotation of its outside walk whose inverse walk reads `R₁ ++ Ā₁ ++ R₂ ++ Ā₂`, with `A₁` an arc
  of `Π_i` and `A₂` an arc of `Π_j`;
* each chunk `R_t` reversing darts of one far side (`a.sideFrom j` or `b.sideFrom i`), or, with a
  run empty, `R₁ ++ R₂` reversing darts of the two far sides;
* when both arcs are empty, some cell off `faces`.

It is lane 11's stand-in `SideBoundFourPieceInputStatement` plus that last clause
(`fourPieceInput_of_fourPieceOff`).

## Why it is true

This is the route of the target docstring.  Take the part of the inner pocket
`sideFaces K \ (a ∪ b)` that holds `C`, and fill its lakes.
* Its outside walk reads sub-lists of the far side of `b`, then of `Ḡ₁`, then of the far side of
  `a`, then of `Ḡ₂`, in cyclic order.
* A pinch where a far side meets a gap, or where the far sides meet, cuts off pieces.  The piece
  holding `C` still reads a cyclic sub-word in this order, so some run is empty exactly when a
  chunk mixes the two far sides.
* `Π_i` and `Π_j` lie in `sideOutside K`, so they are not lakes of the pocket, which gives the
  last clause.

The face set is existential on purpose.  A Π_i-boundary loop inside `G₁` encloses a sub-pocket
`P'`, and that sub-pocket is cut off from `C`'s `Q₀`-class by a `Q₀` edge.  The lake fill of that
class alone then reads `Ḡ₁` with the loop skipped, which is not one arc.  The witness here may add
`P'`.

## Why it is strictly smaller in proof content

The reduction `Assembly.innerPocketEnclosed_of_fourPieceOff` proves several things the residual does
not ask for:
* the bounds `|s_t| ≤ ε` and the re-split of mixed chunks (`pocketSideBound`);
* that the cells of nonempty arcs are off the set (`Assembly.cell_face_not_mem_of_arc_on_walk`);
* the rotation to the base point and the normalisation `A₁.length = 0 ∨ 0 < A₂.length`
  (`enclosedNormalForm`).

It is not a restatement.  Its chunks carry region labels, not lengths, and the target may use any
cells and any chunks.

## Degenerate regions (lanes 02 and 04)

The residual uses no connectivity of the `Q₀` map: it does not use lane 01, the touch clause of
lane 02, or lane 04.  So the degenerate branch of `regionCycleTouch` (empty contact arcs and a
far-side loop joined to `K` only outside `Q₀`) is not assumed away.
* In that configuration the witness is the pocket piece holding `C`.
* A region whose cycle is a far-side loop only feeds side chunks.
* If both arcs are empty, the last clause names a cell off the set.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The labelled four-piece reading of an enclosed pocket, with an off cell when both runs are
empty.**  See the module docstring for why it is true and why it is strictly smaller than the
target. -/
def PocketFourPieceOffStatement : Prop :=
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
        ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ)
          (R₁ R₂ : List X.toCombMap.Dart) (A₁ : CyclicArc (cellDarts X i))
          (A₂ : CyclicArc (cellDarts X j)),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            invDarts X (outerWalk.rotate n) =
              R₁ ++ invDarts X A₁.darts ++ R₂ ++ invDarts X A₂.darts ∧
            ((((∀ r ∈ R₁, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                  (∀ r ∈ R₁, X.toCombMap.alpha r ∈ b.sideFrom i)) ∧
                ((∀ r ∈ R₂, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                  (∀ r ∈ R₂, X.toCombMap.alpha r ∈ b.sideFrom i))) ∨
              ((∀ r ∈ R₁ ++ R₂,
                  X.toCombMap.alpha r ∈ a.sideFrom j ∨ X.toCombMap.alpha r ∈ b.sideFrom i) ∧
                (A₁.length = 0 ∨ A₂.length = 0))) ∧
            (A₁.length = 0 → A₂.length = 0 →
              ∃ k₀ : Fin X.rCellCount, (cell X k₀).face ∉ faces)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement

/-- The residual refines lane 11's stand-in for lane 10: drop the off-cell clause. -/
theorem fourPieceInput_of_fourPieceOff (h : PocketFourPieceOffStatement.{u, w, v}) :
    SideBoundFourPieceInputStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨faces, outerWalk, n, R₁, R₂, A₁, A₂, E, hCF, hdec, hcase, _⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  exact ⟨faces, outerWalk, n, R₁, R₂, A₁, A₂, E, hCF, hdec, hcase⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInput_of_fourPieceOff

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
