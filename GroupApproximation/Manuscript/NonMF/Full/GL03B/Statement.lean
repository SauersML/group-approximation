import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.GGT.VanKampen.SurgeryMap
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# The enclosed inner pocket of a cell pocket walk: local statements

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

* `InnerPocketEnclosedTwoArcLocal` restates, word for word, the foreign statement
  `GreendlingerLeaf.P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
  (`GGT/VanKampen/GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`).  That file is a WIP
  snapshot, so it is not imported here.  The two statements are definitionally equal, and
  `Full/GL03B/Endpoint.lean` transfers the proof.
* `InnerPocketEnclosedTwoArcPinchedLocal` is the same statement with the extra hypothesis that the
  complement cycle of the pocket walk does not follow its boundary walk (the pinched case).

Neither is a literature statement.  Both are purely combinatorial clauses about a finite planar map.
-/

namespace GroupApproximation.Full.GL03B

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **The enclosed inner pocket of a cell pocket walk** (local restatement of
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`; Osin, proof of Lemma 9.7(b); `thm:hull`). -/
def InnerPocketEnclosedTwoArcLocal : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : Embedded.RegionCandidate D eps X)
    (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : Embedded.CyclicArc (Embedded.cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : Embedded.CyclicArc (Embedded.cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk →
      (Surgery.MapCollapse.reclosedMap X.toCombMap
          (SimpleClosedWalkSides.sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (Surgery.MapCollapse.reclosedMap X.toCombMap
          (SimpleClosedWalkSides.sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk →
        C.face ∉ a.1 → C.face ∉ b.1 →
        ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
          (k₁ k₂ : Fin X.rCellCount) (A₁ : Embedded.CyclicArc (Embedded.cellDarts X k₁))
          (A₂ : Embedded.CyclicArc (Embedded.cellDarts X k₂)) (s₁ s₂ : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧
            (∃ C' ∈ X.relatorCells, C'.face ∈ faces) ∧
            (Embedded.cell X k₁).face ∉ faces ∧ (Embedded.cell X k₂).face ∉ faces ∧
            Embedded.invDarts X outerWalk =
              s₁ ++ Embedded.invDarts X A₁.darts ++ s₂ ++ Embedded.invDarts X A₂.darts ∧
            s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ (A₁.length = 0 ∨ 0 < A₂.length)

/-- **The pinched enclosed inner pocket.**  `InnerPocketEnclosedTwoArcLocal` with the extra
hypothesis that the complement cycle of the pocket walk does not follow its boundary walk (Osin,
proof of Lemma 9.7(b); `thm:hull`).  In that case the pocket carries lakes, which must be filled. -/
def InnerPocketEnclosedTwoArcPinchedLocal : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : Embedded.RegionCandidate D eps X)
    (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : Embedded.CyclicArc (Embedded.cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : Embedded.CyclicArc (Embedded.cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk →
      (Surgery.MapCollapse.reclosedMap X.toCombMap
          (SimpleClosedWalkSides.sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (Surgery.MapCollapse.reclosedMap X.toCombMap
          (SimpleClosedWalkSides.sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ¬ (hw.outerCycle X.planar).FollowsBoundary →
      ∀ C ∈ X.relatorCells, C.face ∈ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk →
        C.face ∉ a.1 → C.face ∉ b.1 →
        ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
          (k₁ k₂ : Fin X.rCellCount) (A₁ : Embedded.CyclicArc (Embedded.cellDarts X k₁))
          (A₂ : Embedded.CyclicArc (Embedded.cellDarts X k₂)) (s₁ s₂ : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧
            (∃ C' ∈ X.relatorCells, C'.face ∈ faces) ∧
            (Embedded.cell X k₁).face ∉ faces ∧ (Embedded.cell X k₂).face ∉ faces ∧
            Embedded.invDarts X outerWalk =
              s₁ ++ Embedded.invDarts X A₁.darts ++ s₂ ++ Embedded.invDarts X A₂.darts ∧
            s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ (A₁.length = 0 ∨ 0 < A₂.length)

end GroupApproximation.Full.GL03B
