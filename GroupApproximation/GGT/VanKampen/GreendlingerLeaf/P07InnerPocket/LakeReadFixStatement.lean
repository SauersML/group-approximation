import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.LakeReadStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-42b: the lake reading with a corrected degenerate clause

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

## Uses of the false statement

`PocketFourPieceLakeReadStatement` (`FourPieceOffStatement.lean:72`) is FALSE in its last clause
(lane gl-p07-18, `LakeReadStatement.lean`).  It is a hypothesis of exactly three theorems:
* `pocketFourPieceOff_of_lakeRead` (`FourPieceOff.lean:66`), target `PocketFourPieceOffStatement`;
* `innerPocketEnclosed_of_lakeRead` (`FourPieceOffEndpoint.lean:24`), which composes the first;
* `lakeReadCore_of_lakeRead` (`LakeReadEndpoint.lean:46`), a weakening only.
So the only downstream consumer is `PocketFourPieceOffStatement`, the open 07 row of
`AssemblyResidual.relativeGreendlinger_of_residuals`.  `LakeReadFixRoute.lean` feeds it without
any lake statement; this file and `LakeReadFixOff.lean` repair the lake route itself.

## The false clause and its correction

The false clause asks, when a contact arc on `Π_i` is empty and the lake-fill reading has
`A₁ = A₂ = 0`, for a relator cell off the lake fill `absorbed (sideFaces L) o`.  In the gl-p07-18
model (`Π_i`, `Π_j` hang off `K` at one vertex each, the rest of the pocket is one cell `C`) the lake
fill of `L = ∂C` swallows `Π_i` and `Π_j`, and no cell is off it.

`LakeReadFixStatement` keeps every other clause and replaces that off cell by **an alternative
witness**: some enclosed face set `faces ∋ C` with its own four-piece reading and the off-cell
clause of `PocketFourPieceOffStatement`.  In the model, `faces = {C}` works: its outside walk reads
`Ā₁`, `Ā₂` as the full boundaries of `Π_i`, `Π_j`, so its off-cell clause is vacuous.

## Truth and strength (LOUD)

* **Strictly weaker than the false target:** `lakeReadFix_of_lakeRead` (the lake fill with the same
  reading is an alternative witness).  The target fails on the gl-p07-18 model, and this statement
  holds there (above).
* **True given two plausibly true statements:** `lakeReadFix_of_core_off` (`LakeReadFixOff.lean`)
  derives it from `PocketFourPieceLakeReadCoreStatement` (the gl-p07-18 correction, supported by
  the docstring argument of `FourPieceOffStatement.lean`) and `PocketFourPieceOffStatement` (true
  by the `AssemblyStatement.lean` argument, since its face set is existential).
* **Not easier than the sound route:** it implies `PocketFourPieceOffStatement`
  (`lakeReadFix_pocketFourPieceOff`), and it is equivalent to the core reading plus
  `PocketFourPieceOffStatement` restricted to degenerate contact arcs on `Π_i`.  The preferred route
  to the 07 row is `LakeReadFixRoute.lean` (the sibling step statements).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent

/-- **The lake reading with the degenerate off-cell clause corrected.**  Every outer walk of the
lake fill of a chosen pocket walk `L` has the four-piece reading.  When a contact arc on `Π_i` is
empty and both read arcs are empty, some enclosed face set `faces ∋ C` (not necessarily the lake
fill) has a four-piece reading and an off cell when its own arcs are empty.  See the module
docstring for why it is true and strictly weaker than `PocketFourPieceLakeReadStatement`. -/
def LakeReadFixStatement : Prop :=
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
                    (A₁.length = 0 ∨ A₂.length = 0))) ∧
                (¬ (0 < (a.cellArcList i).length ∧ 0 < (b.cellArcList i).length) →
                  A₁.length = 0 → A₂.length = 0 →
                  ∃ (faces : Finset X.toCombMap.Face) (outerWalk' : List X.toCombMap.Dart)
                    (n' : ℕ) (R₁' R₂' : List X.toCombMap.Dart) (A₁' : CyclicArc (cellDarts X i))
                    (A₂' : CyclicArc (cellDarts X j)),
                    EnclosedFaceSetSucc X faces outerWalk' ∧ C.face ∈ faces ∧
                      invDarts X (outerWalk'.rotate n') =
                        R₁' ++ invDarts X A₁'.darts ++ R₂' ++ invDarts X A₂'.darts ∧
                      ((((∀ r ∈ R₁', X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                            (∀ r ∈ R₁', X.toCombMap.alpha r ∈ b.sideFrom i)) ∧
                          ((∀ r ∈ R₂', X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                            (∀ r ∈ R₂', X.toCombMap.alpha r ∈ b.sideFrom i))) ∨
                        ((∀ r ∈ R₁' ++ R₂', X.toCombMap.alpha r ∈ a.sideFrom j ∨
                            X.toCombMap.alpha r ∈ b.sideFrom i) ∧
                          (A₁'.length = 0 ∨ A₂'.length = 0))) ∧
                      (A₁'.length = 0 → A₂'.length = 0 →
                        ∃ k₀ : Fin X.rCellCount, (cell X k₀).face ∉ faces))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.LakeReadFixStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
