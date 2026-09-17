import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketCellOffRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillSucc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesSurgery
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane `PocketCellOff`: a pocket cell stays outside the filled pocket

Lane gl-p07-07.  The setting is the hypotheses `Hyp` of `InnerPocketEnclosedTwoArcStatement`, a
face set `P` for the inner pocket, and `F = absorbed P o`, the pocket with its lakes filled.  Here
`P` lies in the side faces of `K` and misses `a`, `b`, `Π_i`, `Π_j`.

## THE LANE TARGET IS FALSE

The lane asks for `Π_i ∉ F ∨ Π_j ∉ F` under `Hyp` alone.  Here is a counterexample.
* **The walk.**  `K = s_1 Ā_1 s_2 Ā_2`, where `Ā_1` and `Ā_2` are the whole boundaries of `Π_i`
  and `Π_j`.  The cells hang inside the pocket at corner vertices.
* **The regions.**  `b` runs along `s_1` and `a` along `s_2`, with empty contact arcs
  (`cellArcList i = cellArcList j = []`), so `G_1`, `G_2` are the full arcs.
* **Hyp holds.**  Both Euler equalities hold, because the outer side is a wedge of the exterior
  and the two cells.
* **The target fails.**  With `P` the pocket faces, the piece of the outer face is `O ∪ a ∪ b`.
  So `Π_i` and `Π_j` are both lakes of `P`, and both lie in `F`.

The lane proposes the corrected disjunct `∨ Piece06.LakeFillOneArcExit eps X`.  When both cells
are lakes, lake filling (`lakeFill_bothLakes`) gives either that exit or Piece06's case (d): every
relator cell is enclosed and the outer walk reads `s_1' s_2'`.  Case (d) is not an exit, and in the
model above it plausibly has no one-arc exit.  So the corrected statement adds the disjunct
`PocketAllCellsEnclosed eps X`, which is exactly case (d).

## What is proved (no residual)

`pocketCellOff : PocketCellOffStatement` gives three conclusions.
1. **Nondegenerate target.**  If `a` and `b` have nonempty arcs on `Π_i`, then `Π_i ∉ F` or
   `Π_j ∉ F` (`pocketCellOff_nondegenerate`).
2. **Corrected target.**  `Π_i ∉ F ∨ Π_j ∉ F`, or `LakeFillOneArcExit`, or
   `PocketAllCellsEnclosed` (`pocketCellOff_or_exit`, via `component_mono` and
   `lakeFill_bothLakes`).
3. **Cells met by the outer walk.**  Take a walk whose darts lie on faces off `F`, as for the outer
   walk of `F` (`EnclosedFaceSet.mem_iff`).  If a dart `d` has `α d` on `Π_k`, then `Π_k ∉ F`
   (`not_mem_absorbed_of_alpha_mem_invDarts`).

The downstream lane instantiates `P := sideFaces M L` (lanes 03/05) and discharges `hP`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent

section Exit

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Piece06 case (d)**: an enclosed face set holding every relator cell, with inverse outer walk
`s_1 s_2` and `|s_1|, |s_2| ≤ ε`.  This is the extra disjunct the corrected target needs. -/
def PocketAllCellsEnclosed (eps : ℕ) (X : DiscDiagram.{u, w, v} W) : Prop :=
  ∃ (faces : Finset X.toCombMap.Face) (outerWalk s₁ s₂ : List X.toCombMap.Dart),
    EnclosedFaceSetSucc X faces outerWalk ∧ (∃ C ∈ X.relatorCells, C.face ∈ faces) ∧
      (∀ k : Fin X.rCellCount, (cell X k).face ∈ faces) ∧ invDarts X outerWalk = s₁ ++ s₂ ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps

variable {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The corrected target**: a pocket cell is off the filled pocket, or lake filling gives a
one-arc exit or case (d). -/
theorem pocketCellOff_or_exit (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) {P : Finset X.toCombMap.Face}
    (hPQ : P ⊆ sideFaces X.toCombMap K.walk) :
    ((cell X i).face ∉ absorbed X.toCombMap P X.outerFace ∨
        (cell X j).face ∉ absorbed X.toCombMap P X.outerFace) ∨
      Piece06.LakeFillOneArcExit eps X ∨ PocketAllCellsEnclosed eps X := by
  by_cases h : (cell X i).face ∉ absorbed X.toCombMap P X.outerFace ∨
      (cell X j).face ∉ absorbed X.toCombMap P X.outerFace
  · exact Or.inl h
  · right
    have hi : (cell X i).face ∉ component X.toCombMap P X.outerFace :=
      mem_absorbed_iff.mp (not_not.mp fun hn => h (Or.inl hn))
    have hj : (cell X j).face ∉ component X.toCombMap P X.outerFace :=
      mem_absorbed_iff.mp (not_not.mp fun hn => h (Or.inr hn))
    obtain ⟨faces, outerWalk, s₁, s₂, E, hC, hs₁, hs₂, hk⟩ :=
      P07LakeExclusion.LakeFill.lakeFill_bothLakes K hw hout
        (fun hc => hi (component_mono hPQ hout hc)) (fun hc => hj (component_mono hPQ hout hc))
    rcases hk with ⟨k, A, hkf, hdec⟩ | ⟨hall, hdec⟩
    · exact Or.inl ⟨faces, outerWalk, s₁, s₂, k, A, E, hC, hkf, hdec, hs₁, hs₂⟩
    · exact Or.inr ⟨faces, outerWalk, s₁, s₂, E, hC, hall, hdec, hs₁, hs₂⟩

end Exit

/-- **The pocket cells and the filled inner pocket (corrected).**  The hypotheses of
`InnerPocketEnclosedTwoArcStatement`, a face set `P` in the side faces of `K` that misses `a`, `b`,
`Π_i`, `Π_j`, and a walk on faces off `F = absorbed P o`.  The conclusions are the three listed in
the module docstring.  The plain lane target `Π_i ∉ F ∨ Π_j ∉ F` is FALSE without the extra
disjuncts or the nonempty-arc hypotheses. -/
def PocketCellOffStatement : Prop :=
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
      ∀ P : Finset X.toCombMap.Face,
        (∀ f ∈ P, f ∈ sideFaces X.toCombMap K.walk ∧ f ∉ a.1 ∧ f ∉ b.1 ∧
          f ≠ (cell X i).face ∧ f ≠ (cell X j).face) →
        ∀ outerWalk : List X.toCombMap.Dart,
          (∀ d ∈ outerWalk, X.toCombMap.faceOf d ∉ absorbed X.toCombMap P X.outerFace) →
          (0 < (a.cellArcList i).length → 0 < (b.cellArcList i).length →
              ((cell X i).face ∉ absorbed X.toCombMap P X.outerFace ∨
                (cell X j).face ∉ absorbed X.toCombMap P X.outerFace)) ∧
            (((cell X i).face ∉ absorbed X.toCombMap P X.outerFace ∨
                (cell X j).face ∉ absorbed X.toCombMap P X.outerFace) ∨
              Piece06.LakeFillOneArcExit eps X ∨ PocketAllCellsEnclosed eps X) ∧
            ∀ k : Fin X.rCellCount,
              (∃ d ∈ outerWalk, X.toCombMap.alpha d ∈ invDarts X (cellDarts X k)) →
                (cell X k).face ∉ absorbed X.toCombMap P X.outerFace

/-- **Proof of `PocketCellOffStatement`.** -/
theorem pocketCellOff : PocketCellOffStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi _ _ _ hfirst hsecond _ _ hw hout _ _ _ _ _ _ _
    P hP outerWalk hwalk
  refine ⟨fun hapos hbpos => ?_, pocketCellOff_or_exit K hw hout (fun f hf => (hP f hf).1), ?_⟩
  · simp only [mem_absorbed_iff, not_not]
    exact pocketCellOff_nondegenerate K hij hai hbi hfirst hsecond hw hout hP hapos hbpos
  · rintro k ⟨d, hd, hαd⟩
    have hc : X.toCombMap.faceOf d ∈ component X.toCombMap P X.outerFace := by
      have h := hwalk d hd
      rwa [mem_absorbed_iff, not_not] at h
    exact not_mem_absorbed_of_alpha_mem_invDarts hc hαd

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketAllCellsEnclosed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketCellOff_or_exit
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketCellOffStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketCellOff
