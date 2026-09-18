import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AssemblyStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-20a: splitting the four-piece off statement

The target is `PocketFourPieceOffStatement` (`AssemblyStatement.lean`), the piece-07 residual of
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  This file splits it into a reading part
and a degenerate off-cell part, with the same witness face set for both.

## LOUD: neither existing input statement composes with an off-cell clause

The off-cell clause must hold for the face set of the reading.  So it has to be a claim about every
face set that carries the reading.  In that form it is FALSE over the two existing input statements.
* **The model** is lane gl-p07-18's wedge (`LakeReadStatement.lean`).  Here `K = s₁ Ā₁ s₂ Ā₂`, with
  `Ā₁`, `Ā₂` the full boundaries of `Π_i`, `Π_j`.  Each cell hangs off the contour at one vertex.
  `b` and `a` are strips along `s₁` and `s₂`, and the rest of the pocket is one relator cell `C`.
* **The bad witness.**  Take `faces = {C, Π_i, Π_j}`.  It is an enclosed face set: the loops around
  `Π_i`, `Π_j` are interior.  Its outside walk reads the far side of `b`, then the far side of `a`,
  so `A₁ = A₂ = 0`.  Every relator cell is in `faces`.
* This is the lake fill of `PocketFourPieceLakeReadSomeStatement`.  It also satisfies
  `SideBoundFourPieceInputStatement`.  So neither statement's witness yields the last clause.

## The truthful split

The extra witness clause is: **if both arcs are empty, `faces ⊆ sideFaces K.walk`.**
* `PocketFourPieceInsideStatement`: lane 11's `SideBoundFourPieceInputStatement` plus that clause.
* `PocketFourPieceOffCellStatement`: under the premise block of `PocketFourPieceOffStatement`, every
  face set that carries the reading, has both arcs empty and lies in `sideFaces K.walk` misses some
  relator cell.  It is proved in `FourPieceOffCell.lean`: `Π_i` is off `sideFaces K.walk`.
* `pocketFourPieceOff_of_input_offCell`: the two give `PocketFourPieceOffStatement`.

## Why `PocketFourPieceInsideStatement` is true

The route is that of `AssemblyStatement.lean`, with the witness kept on the side of `K`.
* **Wedge model.**  `faces = {C}` lies in `sideFaces K` and is enclosed, since `EnclosedFaceSet`
  allows pinched walks.  Its outside walk reads the far side of `b`, the loop of `Π_i`, the far side
  of `a`, the loop of `Π_j`.  So `A₁`, `A₂` are the full arcs, and the clause holds.
* **Self-pinch model** (`FourPieceOffStatement.lean`).  The sub-pocket `P'` cut off by a loop of
  `G₁` lies on the side of `K`, because its faces are reached from darts of `K` across edges off
  `K`.  So the witness `Q ∪ P'` stays inside.
* **In general.**  Take the lake fill `absorbed P o` of the pocket piece `P ∋ C`, and intersect it
  with `sideFaces K`.  A lake `f ∈ sideOutside K` of `P` borders `P` only across edges of `K`: the
  side `sideFaces K` is closed under crossing edges off `K`.  So such a lake meets the rest of the
  fill only at pinch vertices of the walk, and leaving it out keeps a single outside walk.  Where
  it is left out, its arc is read as a cell arc.

The lake fill itself (`exists_lakeFill_of_noncrossing`) can hold `Π_i` and `Π_j`, as the wedge
model shows.  So a proof of the reading part through `absorbed` must first cut the fill down to
`sideFaces K`.

## Why the split is strictly smaller in proof content

`pocketFourPieceOff_of_input_offCell` and `pocketFourPieceOffCell` prove the off-cell clause from
the inside clause.  The reading part is only asked for the inside clause.  That clause is a
statement about the witness, not about any relator cell.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The four-piece reading, with the witness on the side of `K` when both arcs are empty.**
This is `SideBoundFourPieceInputStatement` plus the last clause.  See the module docstring for the
truth argument. -/
def PocketFourPieceInsideStatement : Prop :=
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
            (A₁.length = 0 → A₂.length = 0 → faces ⊆ sideFaces X.toCombMap K.walk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceInsideStatement

/-- **The degenerate off-cell clause, for every witness on the side of `K`.**  The premise block is
that of `PocketFourPieceOffStatement`.  Every enclosed face set `faces ∋ C` whose rotated inverse
outside walk reads `R₁ ++ Ā₁ ++ R₂ ++ Ā₂` with both arcs empty, and which lies in
`sideFaces K.walk`, misses some relator cell.  Without the last hypothesis it is false (module
docstring). -/
def PocketFourPieceOffCellStatement : Prop :=
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
        ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ)
          (R₁ R₂ : List X.toCombMap.Dart) (A₁ : CyclicArc (cellDarts X i))
          (A₂ : CyclicArc (cellDarts X j)),
          EnclosedFaceSetSucc X faces outerWalk → C.face ∈ faces →
            invDarts X (outerWalk.rotate n) =
              R₁ ++ invDarts X A₁.darts ++ R₂ ++ invDarts X A₂.darts →
            A₁.length = 0 → A₂.length = 0 → faces ⊆ sideFaces X.toCombMap K.walk →
            ∃ k₀ : Fin X.rCellCount, (cell X k₀).face ∉ faces

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffCellStatement

/-- **The split.**  The reading with the inside clause, and the off-cell clause for inside
witnesses, give `PocketFourPieceOffStatement` with the same witness. -/
theorem pocketFourPieceOff_of_input_offCell (hin : PocketFourPieceInsideStatement.{u, w, v})
    (hoff : PocketFourPieceOffCellStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hout
    hinner houter C hC hCf hCa hCb
  obtain ⟨faces, outerWalk, n, R₁, R₂, A₁, A₂, E, hCF, hdec, hcase, hsub⟩ :=
    hin D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hout hinner houter C hC
      hCf hCa hCb
  refine ⟨faces, outerWalk, n, R₁, R₂, A₁, A₂, E, hCF, hdec, hcase, ?_⟩
  intro hA₁ hA₂
  exact hoff D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hout hinner houter
    C hC hCf hCa hCb faces outerWalk n R₁ R₂ A₁ A₂ E hCF hdec hA₁ hA₂ (hsub hA₁ hA₂)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceOff_of_input_offCell

/-- The inside reading refines lane 11's stand-in: drop the inside clause. -/
theorem fourPieceInput_of_inside (h : PocketFourPieceInsideStatement.{u, w, v}) :
    SideBoundFourPieceInputStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hout
    hinner houter C hC hCf hCa hCb
  obtain ⟨faces, outerWalk, n, R₁, R₂, A₁, A₂, E, hCF, hdec, hcase, _⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hout hinner houter C hC hCf
      hCa hCb
  exact ⟨faces, outerWalk, n, R₁, R₂, A₁, A₂, E, hCF, hdec, hcase⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInput_of_inside

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
