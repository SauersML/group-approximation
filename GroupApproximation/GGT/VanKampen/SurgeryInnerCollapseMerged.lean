import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapseDarts
import GroupApproximation.GGT.VanKampen.SingletonFaceBoundary
import GroupApproximation.Meta.AxiomGuard

/-!
# The merged face of an inner G-region collapse

After `InnerGRegion.diagram` collapses a G-cell region into one face, that face
(`R.merged`) is where the surgery of Osin's Appendix (arXiv:math/0411039v3, Lemma 9.4
Case 1 and the merges of Lemma 9.7(a)) inserts its connector words.  A word insertion
(`GFaceWordInsertion`) asks three things of the face it crosses, and this file supplies
all three:

* it is not the exterior (`merged_ne_outer`);
* it carries no relator cell (`merged_not_relatorFace`);
* it is a G-face, with trivial boundary value (`merged_value`).

It also has no internally paired dart (`merged_noInternalFaceDart`): every dart on the
merged face is a boundary dart of the collapsed region, whose reverse lies on a kept
face.  This is what `Embedded.FaceSetBoundary.ofSingleton` needs to read a face made from
the merged face as a contiguity region.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion

open MapCollapse
open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  (R : InnerGRegion Delta)

/-- A dart of the collapse on the merged face is based, before the collapse, inside the
region. -/
theorem faceOf_val_mem_of_merged {x : R.diagram.toCombMap.Dart}
    (hx : R.diagram.toCombMap.faceOf x = R.merged) :
    Delta.toCombMap.faceOf (R.val x) ∈ R.faces := by
  by_contra hnot
  exact R.kept_ne_merged _ hnot ((R.faceOf_val_not_mem x hnot).symm.trans hx)

/-- **The merged face has no internally paired dart.** -/
theorem merged_noInternalFaceDart :
    NoInternalFaceDart R.diagram.toCombMap R.merged := by
  intro x hx halpha
  have hmem := R.faceOf_val_mem_of_merged hx
  have hout : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (R.val x)) ∉ R.faces :=
    fun h => R.val_not_internal x ⟨hmem, h⟩
  have hout' : Delta.toCombMap.faceOf (R.val (R.diagram.toCombMap.alpha x)) ∉ R.faces := by
    rw [R.val_alpha]
    exact hout
  exact R.kept_ne_merged _ hout'
    ((R.faceOf_val_not_mem (R.diagram.toCombMap.alpha x) hout').symm.trans halpha)

/-- The merged face is not the exterior. -/
theorem merged_ne_outer : R.merged ≠ R.diagram.outerFace :=
  R.newFace_ne_outer

/-- No relator cell of the collapse sits on the merged face. -/
theorem merged_not_relatorFace :
    ∀ C ∈ R.diagram.relatorCells, C.face ≠ R.merged := by
  intro C hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  change R.face C₀.face ≠ R.merged
  rw [R.face_of_not_mem (R.cells_avoid C₀ hC₀)]
  exact R.kept_ne_merged _ _

/-- The merged face is a G-face. -/
theorem merged_value :
    RelLetter.listVal (R.diagram.faceWord R.merged) = 1 :=
  R.newFace_value

end GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.merged_noInternalFaceDart
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.merged_not_relatorFace
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.merged_value
