import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the lake-filled pocket holding the kept cell

Lane `gl-p07-06` of the route 3 cartography (`lanes/carto-gl-p07.md`), infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (`P07LakeExclusion/InnerTwoArcLong.lean`),
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

## Statement

Let `L` be a noncrossing closed walk of the diagram `X` whose side does not contain the outer face
`o`, and let `f` be a face on the side of `L`.  Write `S = sideFaces L`, `P = component S o` (the
exterior piece) and `F = absorbed S o` (the side with every lake filled).  Then there is an outer
walk `W` with
* `EnclosedFaceSetSucc X F W`;
* `f ∈ F`;
* `d ∈ W ↔ α d ∈ L ∧ faceOf d ∈ P`.

In the lane, `L` is the pocket face orbit `L_C` of lanes 04/05 and `f` is the face of the kept cell
`C`; lane 05 supplies `IsNoncrossingClosedWalk L`, `o ∉ sideFaces L`, and `sideFaces L = cls C`,
which contains `C.face`.  `PocketLakeFillStatement` states this under the full hypothesis block of
`InnerPocketEnclosedTwoArcStatement`, universally in `L`, with the three properties of lane 05
as hypotheses on `L`; so it is proved here unconditionally (`pocketLakeFill`) and no interface of
another lane is assumed.

## Proof

1. The exterior piece meets the walk: some dart `d` has `α d ∈ L` and `faceOf d ∈ P`
   (`LakeFill.exists_alpha_mem_component`).  So `x₀ = ⟨d, α d ∈ L⟩` is a dart of the walk map with
   face in `P`.
2. `W = lakeWalk L x₀`, the orbit of `x₀` under the face permutation of the walk map, is the outer
   walk of an `EnclosedFaceSetSucc` of `F` (`LakeFill.lakeWalk_enclosedFaceSetSucc`), and its darts
   are those described (`LakeFill.mem_lakeWalk_iff`).
3. Filling lakes keeps the side, since `o ∉ S` (`ExteriorComponent.subset_absorbed`); so `f ∈ F`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

section General

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The lake-filled side of a noncrossing closed walk**, holding a given side face.  The outer
walk is `lakeWalk` started at a walk-edge dart facing the exterior piece. -/
theorem exists_lakeFill_of_noncrossing (X : DiscDiagram.{u, w, v} W)
    {L : List X.toCombMap.Dart} (hL : IsNoncrossingClosedWalk X.toCombMap L)
    (hout : X.outerFace ∉ sideFaces X.toCombMap L) {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap L) :
    ∃ outerWalk : List X.toCombMap.Dart,
      EnclosedFaceSetSucc X (absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace)
          outerWalk ∧
        f ∈ absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace ∧
        ∀ d : X.toCombMap.Dart, d ∈ outerWalk ↔ X.toCombMap.alpha d ∈ L ∧
          X.toCombMap.faceOf d ∈ component X.toCombMap (sideFaces X.toCombMap L) X.outerFace := by
  obtain ⟨d, hα, hc⟩ := exists_alpha_mem_component hL X.planar hout
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : (walkMap X.toCombMap L).Dart, X.toCombMap.faceOf x₀.1 ∈
      component X.toCombMap (sideFaces X.toCombMap L) X.outerFace :=
    ⟨⟨d, Or.inr hα⟩, hc⟩
  exact ⟨lakeWalk X.toCombMap L x₀, lakeWalk_enclosedFaceSetSucc X hL hout hx₀,
    subset_absorbed hout hf, mem_lakeWalk_iff hL X.planar hout hx₀⟩

end General

/-- **The lake-filled pocket is an enclosed face set holding the kept cell** (lane `gl-p07-06`).
Under the hypothesis block of `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`, for every
noncrossing closed walk `L` (in the lane: the pocket face orbit `L_C`) whose side holds the kept cell
`C` and not the outer face, the lake filling `F = absorbed (sideFaces L) o` of its side is an
`EnclosedFaceSetSucc` over an outer walk whose darts are the reverses of `L`-darts facing the
exterior piece, and `F` holds `C`.
* **Why it is true.**  `exists_lakeFill_of_noncrossing`; the pocket hypotheses are not needed.
* **How lane 15 uses it.**  Apply it to lane 04's `L_C` with lane 05's clauses
  `IsNoncrossingClosedWalk L_C`, `o ∉ sideFaces L_C`, and `C.face ∈ cls C = sideFaces L_C`. -/
def PocketLakeFillStatement : Prop :=
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
        ∀ L : List X.toCombMap.Dart, IsNoncrossingClosedWalk X.toCombMap L →
          X.outerFace ∉ sideFaces X.toCombMap L → C.face ∈ sideFaces X.toCombMap L →
          ∃ outerWalk : List X.toCombMap.Dart,
            EnclosedFaceSetSucc X (absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace)
                outerWalk ∧
              C.face ∈ absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace ∧
              (∃ C' ∈ X.relatorCells,
                C'.face ∈ absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace) ∧
              ∀ d : X.toCombMap.Dart, d ∈ outerWalk ↔ X.toCombMap.alpha d ∈ L ∧
                X.toCombMap.faceOf d ∈
                  component X.toCombMap (sideFaces X.toCombMap L) X.outerFace

/-- **Lane `gl-p07-06`, closed.** -/
theorem pocketLakeFill : PocketLakeFillStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K _ _ _ _ _ _ _ _ _ _ _ _ _ _ C hC _ _ _ L hL hLout hCL
  obtain ⟨outerWalk, E, hCF, hmem⟩ := exists_lakeFill_of_noncrossing X hL hLout hCL
  exact ⟨outerWalk, E, hCF, ⟨C, hC, hCF⟩, hmem⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.exists_lakeFill_of_noncrossing
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLakeFillStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketLakeFill
