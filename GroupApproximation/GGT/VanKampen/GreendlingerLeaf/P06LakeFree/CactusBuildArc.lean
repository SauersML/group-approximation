import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactusStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.DefComponent
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus build: arc entries of the lake-filled walk (lane gl-p06-15)

List and face facts for `P06LakeFree.cellPocketLakeFreeCactusOrder_of_cactusPetal`
(`P06LakeFree/CactusBuildStatement.lean`).  Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b), items 3 and 5 of the truth check of `P06LakeFree/EnclosedOrder.lean`.

## The mathematical proof

Let `K` be a lake-free cell pocket face set, `L` a closed walk with `sideFaces L ⊆ K.faces`, and
`W` a walk with `d ∈ W ↔ ᾱd ∈ L ∧ faceOf d ∈ component (sideFaces L) o` (the lake-filled outer
walk of `P07InnerPocket.exists_lakeFill_of_noncrossing`).  Let `c` be a cell whose face is off
`K.faces` (`Π_i` or `Π_j`) and `A` an arc of its boundary.

1. *A dart on `A` lies on `Π_c`* (`faceOf_of_mem_arc`): `A.darts` is a piece of a rotation of the
   face walk of `Π_c` (`CyclicArc.mem_cycle_of_mem_darts`).
2. *An entry of `invDarts A` on `L` is an entry of `invDarts W`* (`mem_lakeWalk_of_mem_arc`).  Let
   `e ∈ invDarts A` with `e ∈ L`.  Then `ᾱe ∈ A`, so `faceOf ᾱe = Π_c ∉ K.faces`.  By lake
   freeness `Π_c` lies in the exterior piece of `K.faces`, which is inside the exterior piece of the
   smaller set `sideFaces L` (`component_subset_of_subset`).  So `ᾱe` satisfies both clauses of `W`
   (`ᾱᾱe = e ∈ L`), hence `ᾱe ∈ W` and `e ∈ invDarts W`.  Rotations change no entries.
3. *Convexity passes to the lake-filled walk* (`runConvex_lakeWalk`).  If `invDarts W' <+ L'`
   (rotations `W'`, `L'` of `W`, `L`) and `L'` is convex in `invDarts A`, then so is `invDarts W'`:
   by item 2 and the sublist, both walks have the same entries on `invDarts A`
   (`OrderCactus.RunConvex.mono`).  Convexity is NOT monotone under sublists in general
   (`[a, c]` is not convex in `[a, b, c]`), so item 2 is needed.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CactusBuild

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- A dart of an arc of a cell lies on that cell. -/
theorem faceOf_of_mem_arc {c : Fin X.rCellCount} (arc : CyclicArc (cellDarts X c))
    {d : X.toCombMap.Dart} (hd : d ∈ arc.darts) :
    X.toCombMap.faceOf d = (cell X c).face :=
  ((X.faceBoundary (cell X c).face).mem_iff d).mp (arc.mem_cycle_of_mem_darts hd)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CactusBuild.faceOf_of_mem_arc

/-- **Arc entries of a walk inside `K` survive lake filling.**  If `sideFaces L ⊆ K.faces`, `K`
is lake free, and the face of the cell `c` is off `K.faces`, then an entry of `invDarts A` (for an
arc `A` of `c`) lying on `L` lies on the inverse of every lake-filled outer walk of `sideFaces L`,
up to rotations. -/
theorem mem_lakeWalk_of_mem_arc {K : CellPocketFaceSet D eps X i j}
    (hfree : CellPocketLakeFree K) {L ow : List X.toCombMap.Dart}
    (hsub : sideFaces X.toCombMap L ⊆ K.faces)
    (hmem : ∀ d : X.toCombMap.Dart, d ∈ ow ↔ X.toCombMap.alpha d ∈ L ∧
      X.toCombMap.faceOf d ∈
        ExteriorComponent.component X.toCombMap (sideFaces X.toCombMap L) X.outerFace)
    {c : Fin X.rCellCount} (hc : (cell X c).face ∉ K.faces) (arc : CyclicArc (cellDarts X c))
    (n m : ℕ) :
    ∀ e ∈ invDarts X arc.darts, e ∈ L.rotate m → e ∈ invDarts X (ow.rotate n) := by
  intro e he heL
  have ha : X.toCombMap.alpha e ∈ arc.darts := by
    unfold invDarts at he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    rw [X.toCombMap.alpha_involutive x]
    exact List.mem_reverse.mp hx
  have hw : X.toCombMap.alpha e ∈ ow.rotate n := by
    refine List.mem_rotate.mpr ((hmem _).mpr ⟨?_, ?_⟩)
    · rw [X.toCombMap.alpha_involutive e]
      exact List.mem_rotate.mp heL
    · rw [faceOf_of_mem_arc arc ha]
      exact component_subset_of_subset hsub K.outerFace_not_mem (hfree _ hc)
  unfold invDarts
  exact List.mem_map.mpr ⟨X.toCombMap.alpha e, List.mem_reverse.mpr hw,
    X.toCombMap.alpha_involutive e⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CactusBuild.mem_lakeWalk_of_mem_arc

/-- **Convexity passes from `L` to its lake-filled walk.**  If a rotation of the inverse of the
lake-filled walk is a sublist of a rotation of `L`, and the latter is convex in `invDarts A` for an
arc `A` of a cell off `K.faces`, then so is the former. -/
theorem runConvex_lakeWalk {K : CellPocketFaceSet D eps X i j}
    (hfree : CellPocketLakeFree K) {L ow : List X.toCombMap.Dart}
    (hsub : sideFaces X.toCombMap L ⊆ K.faces)
    (hmem : ∀ d : X.toCombMap.Dart, d ∈ ow ↔ X.toCombMap.alpha d ∈ L ∧
      X.toCombMap.faceOf d ∈
        ExteriorComponent.component X.toCombMap (sideFaces X.toCombMap L) X.outerFace)
    {c : Fin X.rCellCount} (hc : (cell X c).face ∉ K.faces) (arc : CyclicArc (cellDarts X c))
    {n m : ℕ} (hsl : (invDarts X (ow.rotate n)).Sublist (L.rotate m))
    (hA : OrderCactus.RunConvex (L.rotate m) (invDarts X arc.darts)) :
    OrderCactus.RunConvex (invDarts X (ow.rotate n)) (invDarts X arc.darts) :=
  hA.mono (mem_lakeWalk_of_mem_arc hfree hsub hmem hc arc n m) fun _ he => hsl.subset he

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CactusBuild.runConvex_lakeWalk

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CactusBuild
