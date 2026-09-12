import GroupApproximation.GGT.VanKampen.SurgeryGFaceMerge
import GroupApproximation.GGT.VanKampen.SingletonFaceBoundary
import GroupApproximation.Meta.AxiomGuard

/-!
# The merged face of a G-face merge

After `Surgery.GFaceMerge.diagram` deletes the edge between two G-faces, the merged face
(`R.merged`) is where Osin's Lemma 9.4 (arXiv:math/0411039v3, §9) inserts its connector words.
`SurgeryGFaceMerge` already shows that the merged face is not the exterior, carries no relator
cell and has trivial boundary value.  This file adds the fourth input of a word insertion: the
merged face has no internally paired dart (`merged_noInternalFaceDart`), provided the deleted
edge is the only edge whose two sides both lie on the two old faces.

* `faceOf_val_of_merged`: a dart of the merge on the merged face comes from one of the two
  old faces;
* `merged_noInternalFaceDart`: under the single-edge hypothesis, in the form it is supplied;
* `merged_noInternalFaceDart_of_sides`: from no internally paired dart on either old face and
  a single edge from the first old face to the second.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge

open MapCollapse

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  (R : GFaceMerge Delta)

/-- A dart of the merge on the merged face comes, before the merge, from one of the two old
faces. -/
theorem faceOf_val_of_merged {x : R.diagram.toCombMap.Dart}
    (hx : R.diagram.toCombMap.faceOf x = R.merged) :
    Delta.toCombMap.faceOf (R.val x) = R.first ∨ Delta.toCombMap.faceOf (R.val x) = R.second := by
  by_contra h
  rw [not_or] at h
  exact R.kept_ne_merged h ((R.faceOf_val_kept x h).symm.trans hx)

/-- **The merged face has no internally paired dart**, when the deleted edge is the only edge
with both sides on the two old faces. -/
theorem merged_noInternalFaceDart
    (hsingle : ∀ d : Delta.toCombMap.Dart,
      (Delta.toCombMap.faceOf d = R.first ∨ Delta.toCombMap.faceOf d = R.second) →
      (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = R.first ∨
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = R.second) →
      d = R.dart ∨ d = Delta.toCombMap.alpha R.dart) :
    NoInternalFaceDart R.diagram.toCombMap R.merged := by
  intro x hx halpha
  have h1 := R.faceOf_val_of_merged hx
  have h2 := R.faceOf_val_of_merged halpha
  rw [R.val_alpha] at h2
  rcases hsingle (R.val x) h1 h2 with h | h
  · exact (R.val_ne x).1 h
  · exact (R.val_ne x).2 h

/-- The merged face has no internally paired dart when neither old face has one and the
deleted edge is the only edge from the first old face to the second. -/
theorem merged_noInternalFaceDart_of_sides
    (h1 : NoInternalFaceDart Delta.toCombMap R.first)
    (h2 : NoInternalFaceDart Delta.toCombMap R.second)
    (hedge : ∀ d : Delta.toCombMap.Dart, Delta.toCombMap.faceOf d = R.first →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = R.second → d = R.dart) :
    NoInternalFaceDart R.diagram.toCombMap R.merged := by
  refine R.merged_noInternalFaceDart fun d hd hda => ?_
  rcases hd with hd | hd <;> rcases hda with hda | hda
  · exact absurd hda (h1 d hd)
  · exact Or.inl (hedge d hd hda)
  · have h := hedge (Delta.toCombMap.alpha d) hda
      (by rw [Delta.toCombMap.alpha_involutive d]; exact hd)
    exact Or.inr ((Delta.toCombMap.alpha_involutive d).symm.trans
      (congrArg Delta.toCombMap.alpha h))
  · exact absurd hda (h2 d hd)

end GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.faceOf_val_of_merged
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.merged_noInternalFaceDart
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.merged_noInternalFaceDart_of_sides
