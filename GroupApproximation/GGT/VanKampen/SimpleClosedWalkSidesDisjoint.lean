import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Disjoint sides of two closed walks with barrier faces

Osin, arXiv:math/0411039v3, §9, Lemma 9.4, Case 1, for a backwards connector pair whose two sides
lie across one relator cell `Π`.  Some rotation of the boundary walk of the polygon face `f` reads
`X q⁻¹ Y p⁻¹`, and some rotation of `∂Π` reads `q B p A`, so `X B` and `Y A` are closed walks.
The pocket walks are `invDarts X ++ invDarts B` and `invDarts Y ++ invDarts A`.  The faces across
either walk are `f` and `Π`, and a pocket region is the side of one walk that avoids the exterior
face.  This file shows that the two sides are disjoint, so the exterior face is off one of them.

The argument is about face classes only.  The side of a walk `w` is a union of face classes of
`walkKeep M w` (`mem_sideFaces_iff_of_eqvGen`).  If the faces across `w₁` are off the side of
`w₂`, a face-class chain of `w₂` that starts on the side of `w₂` never crosses an edge of `w₁`
(`eqvGen_walkKeep_of_mem_sideFaces`), so it is also a chain of `w₁`.

* `SimpleClosedWalkSides.disjoint_sideFaces_of_across`: the sides are disjoint when the faces
  across each walk are off the side of the other and no edge of `w₂` is an edge of `w₁`.
* `SimpleClosedWalkSides.not_walkKeep_of_across` and `disjoint_sideFaces_of_across_of_not_mem`:
  a dart of `w₂` reversed on `w₁` contradicts the first barrier condition, so it is enough that
  the walks share no dart.
* `SimpleClosedWalkSides.not_mem_sideFaces_or_of_across`: any face, the exterior face included,
  is off one of the two sides.
* `SimpleClosedWalkSides.disjoint_sideFaces_of_barrier`: for simple closed walks in a planar
  map, it is enough that every face across one walk is also across the other.
* `SimpleClosedWalkSides.disjoint_sideFaces_of_barrier_noncrossing` and
  `not_mem_sideFaces_or_of_barrier_noncrossing`: the same for noncrossing closed walks, which may
  touch themselves at a vertex, with no common dart.  For the pocket walks of Case 1 the walks
  share no dart because the face walk and the carrier of the cell have no repeated dart and `f`
  is not `Π`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

namespace SimpleClosedWalkSides

variable {M : CombMap.{u}}

/-- **The side of a walk is a union of face classes.** -/
theorem mem_sideFaces_iff_of_eqvGen (w : List M.Dart) {x z : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x z) :
    M.faceOf x ∈ sideFaces M w ↔ M.faceOf z ∈ sideFaces M w := by
  rw [mem_sideFaces_iff, mem_sideFaces_iff]
  constructor
  · rintro ⟨d, hd, hdx⟩
    exact ⟨d, hd, .trans _ _ _ hdx h⟩
  · rintro ⟨d, hd, hdz⟩
    exact ⟨d, hd, .trans _ _ _ hdz (.symm _ _ h)⟩

/-- **A face-class chain on one side never crosses the other walk.**  If the faces across `w₁`
are off the side of `w₂`, a face-class chain of `w₂` starting on the side of `w₂` crosses no edge
of `w₁`, so it is a face-class chain of `w₁`. -/
theorem eqvGen_walkKeep_of_mem_sideFaces {w₁ w₂ : List M.Dart}
    (hacross : ∀ d ∈ w₁, M.faceOf (M.alpha d) ∉ sideFaces M w₂) {x z : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w₂)) x z) :
    M.faceOf x ∈ sideFaces M w₂ →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w₁)) x z := by
  induction h with
  | rel x₁ x₂ hstep =>
      intro hx
      rcases hstep with hface | ⟨hk₂, rfl⟩
      · exact .rel _ _ (Or.inl hface)
      · have hα : M.faceOf (M.alpha x₁) ∈ sideFaces M w₂ :=
          (mem_sideFaces_iff_of_eqvGen w₂ (.rel _ _ (Or.inr ⟨hk₂, rfl⟩))).mp hx
        refine .rel _ _ (Or.inr ⟨?_, rfl⟩)
        rintro (hmem | hmem)
        · exact hacross x₁ hmem hα
        · have h' := hacross (M.alpha x₁) hmem
          rw [M.alpha_involutive x₁] at h'
          exact h' hx
  | refl x₁ =>
      intro _
      exact .refl _
  | symm x₁ x₂ hrel ih =>
      intro hx
      exact .symm _ _ (ih ((mem_sideFaces_iff_of_eqvGen w₂ hrel).mpr hx))
  | trans x₁ x₂ x₃ h₁₂ _ ih₁ ih₂ =>
      intro hx
      exact .trans _ _ _ (ih₁ hx) (ih₂ ((mem_sideFaces_iff_of_eqvGen w₂ h₁₂).mp hx))

/-- **Two walks with barrier faces have disjoint sides.**  The faces across `w₁` are off the side
of `w₂`, the faces across `w₂` are off the side of `w₁`, and no edge of `w₂` is an edge of `w₁`. -/
theorem disjoint_sideFaces_of_across {w₁ w₂ : List M.Dart}
    (hacross₁ : ∀ d ∈ w₁, M.faceOf (M.alpha d) ∉ sideFaces M w₂)
    (hacross₂ : ∀ d ∈ w₂, M.faceOf (M.alpha d) ∉ sideFaces M w₁)
    (hoff : ∀ d ∈ w₂, ¬ walkKeep M w₁ d) :
    Disjoint (sideFaces M w₁) (sideFaces M w₂) := by
  refine Finset.disjoint_left.mpr fun F hF₁ hF₂ => ?_
  obtain ⟨z, hz⟩ := Quotient.exists_rep F
  have hz' : M.faceOf z = F := hz
  subst hz'
  obtain ⟨d, hd, hdz⟩ := (mem_sideFaces_iff M w₂ z).mp hF₂
  have hd₂ : M.faceOf d ∈ sideFaces M w₂ := (mem_sideFaces_iff M w₂ d).mpr ⟨d, hd, .refl _⟩
  have h₁ := eqvGen_walkKeep_of_mem_sideFaces hacross₁ hdz hd₂
  have hd₁ : M.faceOf d ∈ sideFaces M w₁ := (mem_sideFaces_iff_of_eqvGen w₁ h₁).mpr hF₁
  have hcross : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w₁)) d (M.alpha d) :=
    .rel _ _ (Or.inr ⟨hoff d hd, rfl⟩)
  exact hacross₂ d hd ((mem_sideFaces_iff_of_eqvGen w₁ hcross).mp hd₁)

/-- **A dart reversed on the other walk.**  If the faces across `w₁` are off the side of `w₂` and
the walks share no dart, no dart of `w₂` lies on an edge of `w₁`: a dart `d` of `w₂` with
`alpha d` on `w₁` would put the face of `d`, which is on the side of `w₂`, across `w₁`. -/
theorem not_walkKeep_of_across {w₁ w₂ : List M.Dart}
    (hacross₁ : ∀ d ∈ w₁, M.faceOf (M.alpha d) ∉ sideFaces M w₂)
    (hcommon : ∀ d ∈ w₂, d ∉ w₁) {d : M.Dart} (hd : d ∈ w₂) : ¬ walkKeep M w₁ d := by
  rintro (hmem | hmem)
  · exact hcommon d hd hmem
  · have h := hacross₁ (M.alpha d) hmem
    rw [M.alpha_involutive d] at h
    exact h ((mem_sideFaces_iff M w₂ d).mpr ⟨d, hd, .refl _⟩)

/-- **Two walks with barrier faces and no common dart have disjoint sides.** -/
theorem disjoint_sideFaces_of_across_of_not_mem {w₁ w₂ : List M.Dart}
    (hacross₁ : ∀ d ∈ w₁, M.faceOf (M.alpha d) ∉ sideFaces M w₂)
    (hacross₂ : ∀ d ∈ w₂, M.faceOf (M.alpha d) ∉ sideFaces M w₁)
    (hcommon : ∀ d ∈ w₂, d ∉ w₁) :
    Disjoint (sideFaces M w₁) (sideFaces M w₂) :=
  disjoint_sideFaces_of_across hacross₁ hacross₂
    fun _ hd => not_walkKeep_of_across hacross₁ hcommon hd

/-- **Any face is off one of the two sides**, in the setting of `disjoint_sideFaces_of_across`.
Applied to the exterior face, it picks the side that is a pocket. -/
theorem not_mem_sideFaces_or_of_across {w₁ w₂ : List M.Dart}
    (hacross₁ : ∀ d ∈ w₁, M.faceOf (M.alpha d) ∉ sideFaces M w₂)
    (hacross₂ : ∀ d ∈ w₂, M.faceOf (M.alpha d) ∉ sideFaces M w₁)
    (hoff : ∀ d ∈ w₂, ¬ walkKeep M w₁ d) (F : M.Face) :
    F ∉ sideFaces M w₁ ∨ F ∉ sideFaces M w₂ := by
  by_cases h : F ∈ sideFaces M w₁
  · exact Or.inr (Finset.disjoint_left.mp (disjoint_sideFaces_of_across hacross₁ hacross₂ hoff) h)
  · exact Or.inl h

/-- **Simple closed walks with shared barrier faces have disjoint sides.**  In a planar map, the
face across a dart of a simple closed walk is off its side.  So it is enough that every face across
`w₁` is across some dart of `w₂`, and conversely. -/
theorem disjoint_sideFaces_of_barrier (hM : M.IsPlanar) {w₁ w₂ : List M.Dart}
    (hw₁ : IsSimpleClosedWalk M w₁) (hw₂ : IsSimpleClosedWalk M w₂)
    (hbarrier₁ : ∀ d ∈ w₁, ∃ e ∈ w₂, M.faceOf (M.alpha d) = M.faceOf (M.alpha e))
    (hbarrier₂ : ∀ d ∈ w₂, ∃ e ∈ w₁, M.faceOf (M.alpha d) = M.faceOf (M.alpha e))
    (hoff : ∀ d ∈ w₂, ¬ walkKeep M w₁ d) :
    Disjoint (sideFaces M w₁) (sideFaces M w₂) := by
  have hacross : ∀ {v : List M.Dart}, IsSimpleClosedWalk M v → ∀ e ∈ v,
      M.faceOf (M.alpha e) ∉ sideFaces M v := by
    intro v hv e he
    exact (show M.faceOf e ∈ sideFaces M v ∧ M.faceOf (M.alpha e) ∉ sideFaces M v from
      (hv.isBoundaryDart_sideFaces_iff hM e).mpr he).2
  refine disjoint_sideFaces_of_across (fun d hd => ?_) (fun d hd => ?_) hoff
  · obtain ⟨e, he, hde⟩ := hbarrier₁ d hd
    rw [hde]
    exact hacross hw₂ e he
  · obtain ⟨e, he, hde⟩ := hbarrier₂ d hd
    rw [hde]
    exact hacross hw₁ e he

/-- **Noncrossing closed walks with shared barrier faces and no common dart have disjoint
sides.**  In a planar map, the face across a dart of a noncrossing closed walk is off its side, as
for simple walks. -/
theorem disjoint_sideFaces_of_barrier_noncrossing (hM : M.IsPlanar) {w₁ w₂ : List M.Dart}
    (hw₁ : IsNoncrossingClosedWalk M w₁) (hw₂ : IsNoncrossingClosedWalk M w₂)
    (hbarrier₁ : ∀ d ∈ w₁, ∃ e ∈ w₂, M.faceOf (M.alpha d) = M.faceOf (M.alpha e))
    (hbarrier₂ : ∀ d ∈ w₂, ∃ e ∈ w₁, M.faceOf (M.alpha d) = M.faceOf (M.alpha e))
    (hcommon : ∀ d ∈ w₂, d ∉ w₁) :
    Disjoint (sideFaces M w₁) (sideFaces M w₂) := by
  have hacross : ∀ {v : List M.Dart}, IsNoncrossingClosedWalk M v → ∀ e ∈ v,
      M.faceOf (M.alpha e) ∉ sideFaces M v := by
    intro v hv e he
    exact (show M.faceOf e ∈ sideFaces M v ∧ M.faceOf (M.alpha e) ∉ sideFaces M v from
      (hv.isBoundaryDart_sideFaces_iff hM e).mpr he).2
  refine disjoint_sideFaces_of_across_of_not_mem (fun d hd => ?_) (fun d hd => ?_) hcommon
  · obtain ⟨e, he, hde⟩ := hbarrier₁ d hd
    rw [hde]
    exact hacross hw₂ e he
  · obtain ⟨e, he, hde⟩ := hbarrier₂ d hd
    rw [hde]
    exact hacross hw₁ e he

/-- **Any face is off one of two noncrossing sides**, in the setting of
`disjoint_sideFaces_of_barrier_noncrossing`.  Applied to the exterior face, it gives the input
`hout` of `PocketRegion.ofNoncrossingClosedWalk` for one of the two walks. -/
theorem not_mem_sideFaces_or_of_barrier_noncrossing (hM : M.IsPlanar) {w₁ w₂ : List M.Dart}
    (hw₁ : IsNoncrossingClosedWalk M w₁) (hw₂ : IsNoncrossingClosedWalk M w₂)
    (hbarrier₁ : ∀ d ∈ w₁, ∃ e ∈ w₂, M.faceOf (M.alpha d) = M.faceOf (M.alpha e))
    (hbarrier₂ : ∀ d ∈ w₂, ∃ e ∈ w₁, M.faceOf (M.alpha d) = M.faceOf (M.alpha e))
    (hcommon : ∀ d ∈ w₂, d ∉ w₁) (F : M.Face) :
    F ∉ sideFaces M w₁ ∨ F ∉ sideFaces M w₂ := by
  by_cases h : F ∈ sideFaces M w₁
  · exact Or.inr (Finset.disjoint_left.mp
      (disjoint_sideFaces_of_barrier_noncrossing hM hw₁ hw₂ hbarrier₁ hbarrier₂ hcommon) h)
  · exact Or.inl h

end SimpleClosedWalkSides

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.mem_sideFaces_iff_of_eqvGen
#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.eqvGen_walkKeep_of_mem_sideFaces
#audit_axioms GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.disjoint_sideFaces_of_across
#audit_axioms GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.not_walkKeep_of_across
#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.disjoint_sideFaces_of_across_of_not_mem
#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.not_mem_sideFaces_or_of_across
#audit_axioms GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.disjoint_sideFaces_of_barrier
#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.disjoint_sideFaces_of_barrier_noncrossing
#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.not_mem_sideFaces_or_of_barrier_noncrossing
