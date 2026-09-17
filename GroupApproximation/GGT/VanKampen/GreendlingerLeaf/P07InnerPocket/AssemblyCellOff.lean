import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket assembly: a cell read on the outside walk is off the set

Lane gl-p07-15, helper.  Infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  Certifies no printed sentence on its own.

## The mathematical proof

Let `E : EnclosedFaceSetSucc X F L`.  Let `A` be a nonempty arc of the cell `Π_k`, and suppose every
dart of `invDarts X A.darts` is a dart of `invDarts X (L.rotate m)`.
1. Pick a dart `y` of `A.darts`.  Then `α y ∈ invDarts X A.darts`, so `α y ∈ invDarts X (L.rotate m)`.
2. So `α y = α z` for some `z ∈ (L.rotate m).reverse`, and `z = y` because `α` is injective.
   Hence `y ∈ L` (`List.mem_rotate`).
3. By `mem_iff` of `E`, walk darts are based off `F`, so `faceOf y ∉ F`.
4. `y` is a boundary dart of `Π_k` (`CyclicArc.mem_cycle_of_mem_darts`), so
   `faceOf y = (cell X k).face` (`Embedded.faceOf_of_mem_cellDarts`).

This holds for every face set `F`.  Truth check: the proof uses only the membership clause.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.Assembly

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A nonempty arc read on the outside walk lies on a cell off the enclosed set.** -/
theorem cell_face_not_mem_of_arc_on_walk {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} {L : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F L)
    {k : Fin X.rCellCount} (A : CyclicArc (cellDarts X k)) (m : ℕ)
    (hsub : ∀ x ∈ invDarts X A.darts, x ∈ invDarts X (L.rotate m)) (hpos : 0 < A.length) :
    (cell X k).face ∉ F := by
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil A.darts
    (List.ne_nil_of_length_pos (by rw [CyclicArc.darts_length]; exact hpos))
  have hx : X.toCombMap.alpha y ∈ invDarts X A.darts := by
    unfold invDarts
    exact List.mem_map.mpr ⟨y, List.mem_reverse.mpr hy, rfl⟩
  have hx' : X.toCombMap.alpha y ∈ (L.rotate m).reverse.map X.toCombMap.alpha := hsub _ hx
  obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hx'
  have hzy' : z = y := X.toCombMap.alpha_involutive.injective hzy
  rw [hzy'] at hz
  have hyL : y ∈ L := List.mem_rotate.mp (List.mem_reverse.mp hz)
  have hyF : X.toCombMap.faceOf y ∉ F := ((E.mem_iff y).mp hyL).1
  rwa [Embedded.faceOf_of_mem_cellDarts (A.mem_cycle_of_mem_darts hy)] at hyF

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.Assembly.cell_face_not_mem_of_arc_on_walk

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.Assembly
