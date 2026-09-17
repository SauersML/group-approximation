import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AssemblyStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLakeFill
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketCellOffRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-16: the lake-walk four-piece reading

Lane gl-p07-16 targets `PocketFourPieceOffStatement` (`AssemblyStatement.lean`), the residual of
lane gl-p07-15.  The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).
`FourPieceOff.lean` reduces it to the single residual `PocketFourPieceLakeReadStatement` below.

## Truth check on the self-pinch model (LOUD)

The target is **true only because its face set is existential**.  Over a fixed lake fill
`absorbed (sideFaces K) o` it is FALSE.  Here is why.
* Say `Π_i` pinches at a vertex `v` inside its gap `G₁`.  The loop of `G₁` between the two visits
  of `v` bounds a sub-pocket `P'` that meets the rest of the pocket only at `v`.
* If `P'` is left out, the outer walk skips the loop and reads `Ḡ₁` as `B̄₂ ++ B̄₁`.  That is two
  sub-arcs (lane gl-p07-09), not one `CyclicArc`.
* So the witness must **add `P'`**.  Then the outer walk runs through the loop, and `Ḡ₁` reads as
  one contiguous run.

A self-pinch of a far side is harmless, because the side chunks only need membership.

## The residual

The residual asks for a noncrossing closed walk `L`.  In the model, `L` reverses the boundary
walk of the pocket piece `Q ∋ C` with its self-pinch sub-pockets added.  It must satisfy:
* `C ∈ sideFaces L`;
* every face `f ∈ sideFaces L` lies in `sideFaces K`, off `a`, off `b`, and is not `Π_i` or `Π_j`.

Then, for **every** outer walk of the lake fill `F = absorbed (sideFaces L) o`, the statement asks
for a rotation, chunks and arcs.  "Every outer walk" means every `EnclosedFaceSetSucc F` whose darts
are the reverses of `L`-darts facing the exterior piece.  The last clause is only needed when a
contact arc of `a` or `b` on `Π_i` is empty.

## Why the residual is true

* **The `L` clauses.**  `sideFaces L` is `Q ∪ P'` plus the lakes of `Q`.  All of these lie in the
  side of `K`.  They are off `a`, `b`, `Π_i` and `Π_j`, because those faces are entered only
  across edges of `L`.
* **Every outer walk.**  `turn_next` fixes the successor of each dart from the dart set.  A nodup
  closed chain through the whole set is therefore one orbit, so all such walks are rotations of
  each other.  The reading of one gives the reading of all, after shifting `n`.
* **The reading.**  This is the argument of `AssemblyStatement.lean`, applied to `F`.
* **The degenerate off cell.**  `Π_i` and `Π_j` lie in `sideOutside K`, and `P ⊆ sideFaces K`.
  So the connected outer side joins them to `o` without entering `P`, and they are not absorbed.

## Why the residual is strictly smaller

The reduction `pocketFourPieceOff_of_lakeRead` proves three things the residual does not ask for.
* **The enclosed face set.**  It builds the face set, the full `EnclosedFaceSetSucc` structure
  (chain, closing, `mem_iff`, `turn_mem`, `turn_next`) and `C ∈ F`, by
  `exists_lakeFill_of_noncrossing`.  The residual gets `E` as a hypothesis.
* **The outer face.**  It proves `o ∉ sideFaces L` from `sideFaces L ⊆ sideFaces K`.
* **The nondegenerate off cell.**  When both contact arcs on `Π_i` are nonempty, it proves the
  off-cell clause by lane gl-p07-07's `pocketCellOff_nondegenerate`.  The residual's last clause
  has the extra premise that a contact arc is empty, so that clause is logically weaker.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent

/-- **The four-piece reading of every lake walk of a chosen noncrossing pocket walk `L`**.  The
premise block is that of `PocketFourPieceOffStatement`.  See the module docstring for the truth
argument, with sub-pocket absorption, and for why it is strictly smaller. -/
def PocketFourPieceLakeReadStatement : Prop :=
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
                  ∃ k₀ : Fin X.rCellCount, (cell X k₀).face ∉
                    absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceLakeReadStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
