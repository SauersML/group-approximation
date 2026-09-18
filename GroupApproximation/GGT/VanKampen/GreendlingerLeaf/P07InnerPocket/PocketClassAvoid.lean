import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClassCells
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the pocket class avoids a, b, outside and the two cells

Lane `gl-p07-03` of the route 3 cartography (`lanes/carto-gl-p07.md`), endpoint module.  This is
infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`P07LakeExclusion/InnerTwoArcLong.lean`), from Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  It certifies no printed sentence on its own.

## Statement

`PocketClassAvoidStatement` assumes the full hypothesis block of
`InnerPocketEnclosedTwoArcStatement`, copied verbatim.  Its conclusion concerns
`cls C = PocketClass.pocketClass a b K C.face`, the `Q₀` face class of `C.face` with
`Q₀ = PocketClass.pocketKeep a b K`.

* Every `f ∈ cls C` satisfies `f ∉ a`, `f ∉ b`, `f ∈ sideFaces K.walk`, `f ≠ o`, `f ≠ Π_i` and
  `f ≠ Π_j`.
* No bridge: no `Q₀`-kept dart has both sides in `cls C`.

## Proof route

Introduce the hypotheses and assemble the `PocketClass` lemmas.
* `not_mem_left_of_mem_pocketClass` and `not_mem_right_of_mem_pocketClass` use `C ∉ a`, `C ∉ b`.
* `mem_sideFaces_of_mem_pocketClass` uses `C ∈ sideFaces K.walk`.
* `pocketClass_ne_outerFace` uses `o ∉ sideFaces K.walk`.
* `pocketClass_ne_cell_left` and `pocketClass_ne_cell_right` use that the walk is noncrossing.
* `pocketClass_noBridge` gives the no-bridge clause.

The other hypotheses are unused.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Lane `gl-p07-03`.**  Under the hypotheses of `InnerPocketEnclosedTwoArcStatement`, the
pocket class of `C` avoids both regions, the outer face and the two cells, and lies on the side of
`K.walk`.  No kept edge bridges it. -/
def PocketClassAvoidStatement : Prop :=
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
        (∀ f ∈ PocketClass.pocketClass a b K C.face,
          f ∉ a.1 ∧ f ∉ b.1 ∧ f ∈ sideFaces X.toCombMap K.walk ∧ f ≠ X.outerFace ∧
            f ≠ (cell X i).face ∧ f ≠ (cell X j).face) ∧
        ∀ d, PocketClass.pocketKeep a b K d →
          ¬ (X.toCombMap.faceOf d ∈ PocketClass.pocketClass a b K C.face ∧
            X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ PocketClass.pocketClass a b K C.face)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClassAvoidStatement

/-- **Lane `gl-p07-03`, closed.** -/
theorem pocketClassAvoid : PocketClassAvoidStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K _ _ _ _ _ _ _ _ _ _ hw hoff _ _ C _ hCf hCa hCb
  exact ⟨fun f hf => ⟨PocketClass.not_mem_left_of_mem_pocketClass hCa hf,
      PocketClass.not_mem_right_of_mem_pocketClass hCb hf,
      PocketClass.mem_sideFaces_of_mem_pocketClass hCf hf,
      PocketClass.pocketClass_ne_outerFace hoff hCf hf,
      PocketClass.pocketClass_ne_cell_left hw hCf hf,
      PocketClass.pocketClass_ne_cell_right hw hCf hf⟩,
    fun d hd => PocketClass.pocketClass_noBridge hw hCf hCa hCb d hd⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketClassAvoid

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
