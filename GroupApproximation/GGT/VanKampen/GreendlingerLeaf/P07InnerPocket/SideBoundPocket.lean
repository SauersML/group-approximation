import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLong
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: side chunks bounded by ε, under the pocket hypotheses

Lane `gl-p07-11`, Hyp-level form.  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (`InnerTwoArcLong.lean:55`); certifies no
printed sentence on its own.

Lane 10 (`FourPiece*.lean`) is not on disk yet, so its output is stated here as
`SideBoundFourPieceInputStatement`: under the full hypothesis block of
`InnerPocketEnclosedTwoArcStatement`, the lake-filled pocket (lane 06) is an enclosed face set
`faces ∋ C` with outside walk `outerWalk`, and a rotation of `outerWalk` has inverse walk
`R₁ ++ Ā₁ ++ R₂ ++ Ā₂`, with `A₁` an arc of `Π_i`, `A₂` an arc of `Π_j`, each side chunk reversing
darts of one far side (`a.sideFrom j` or `b.sideFrom i`), or, when a run is empty, `R₁ ++ R₂`
reversing darts of the two far sides.

`boundedFourPiece_of_fourPieceInput` reduces `PocketBoundedFourPieceStatement` (the same data with
`|S₁|, |S₂| ≤ ε`) to it, through the proved `pocketSideBound`.  If lane 10's def has another shape,
lane 15 composes it with `pocketSideBound` directly; only this file would change.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

section Arcs

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- An arc reads no inverse darts exactly when it has length zero. -/
theorem sideBound_invDarts_eq_nil_iff {k : Fin X.rCellCount} (A : CyclicArc (cellDarts X k)) :
    invDarts X A.darts = [] ↔ A.length = 0 := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    simpa only [invDarts, List.length_map, List.length_reverse, A.darts_length,
      List.length_nil] using hlen
  · intro h
    exact List.eq_nil_of_length_eq_zero
      (by simp only [invDarts, List.length_map, List.length_reverse, A.darts_length, h])

end Arcs

/-- **Stand-in for lane 10's four-piece order** (`PocketFourPieceOrderStatement`, not on disk).
Hypotheses: those of `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`.  Conclusion: an enclosed
face set holding `C`, and a rotation of its outside walk whose inverse walk reads
`R₁ ++ Ā₁ ++ R₂ ++ Ā₂` with arcs `A₁` of `Π_i`, `A₂` of `Π_j`, each side chunk reversing darts of one
far side, or, with a run empty, the side chunks reversing darts of the two far sides. -/
def SideBoundFourPieceInputStatement : Prop :=
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
                (A₁.length = 0 ∨ A₂.length = 0)))

/-- **The bounded four-piece decomposition of the pocket.**  Hypotheses: those of
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`.  Conclusion: an enclosed face set holding
`C`, and a rotation of its outside walk whose inverse walk reads `S₁ ++ Ā₁ ++ S₂ ++ Ā₂`, or, with
`A₂` empty, `S₁ ++ ∅ ++ S₂ ++ Ā₁`, where `|S₁|, |S₂| ≤ ε`. -/
def PocketBoundedFourPieceStatement : Prop :=
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
        ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (m : ℕ)
          (S₁ S₂ : List X.toCombMap.Dart) (A₁ : CyclicArc (cellDarts X i))
          (A₂ : CyclicArc (cellDarts X j)),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧ S₁.length ≤ eps ∧
            S₂.length ≤ eps ∧
            (invDarts X (outerWalk.rotate m) =
                S₁ ++ invDarts X A₁.darts ++ S₂ ++ invDarts X A₂.darts ∨
              (A₂.length = 0 ∧
                invDarts X (outerWalk.rotate m) = S₁ ++ [] ++ S₂ ++ invDarts X A₁.darts))

/-- **The bounded four-piece decomposition from lane 10's four-piece order**, by
`pocketSideBound`. -/
theorem boundedFourPiece_of_fourPieceInput (h : SideBoundFourPieceInputStatement.{u, w, v}) :
    PocketBoundedFourPieceStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨faces, outerWalk, n, R₁, R₂, A₁, A₂, E, hCF, hdec, hcase⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  obtain ⟨m, S₁, V₁, S₂, V₂, hdec', hS₁, hS₂, hV⟩ :=
    pocketSideBound D eps X i j a b outerWalk n R₁ (invDarts X A₁.darts) R₂
      (invDarts X A₂.darts) E.nodup hdec (by
        rcases hcase with hc | ⟨hfar, hA⟩
        · exact Or.inl hc
        · exact Or.inr ⟨hfar, hA.imp (sideBound_invDarts_eq_nil_iff A₁).mpr
            (sideBound_invDarts_eq_nil_iff A₂).mpr⟩)
  refine ⟨faces, outerWalk, m, S₁, S₂, A₁, A₂, E, hCF, hS₁, hS₂, ?_⟩
  rcases hV with ⟨rfl, rfl⟩ | ⟨hA₂, rfl, rfl⟩
  · exact Or.inl hdec'
  · exact Or.inr ⟨(sideBound_invDarts_eq_nil_iff A₂).mp hA₂, hdec'⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.sideBound_invDarts_eq_nil_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBoundFourPieceInputStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketBoundedFourPieceStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.boundedFourPiece_of_fourPieceInput
