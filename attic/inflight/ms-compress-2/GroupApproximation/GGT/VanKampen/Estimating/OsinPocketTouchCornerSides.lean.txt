import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTouchCornerThickening
import GroupApproximation.GGT.VanKampen.SurgeryCellEdgeThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# The side of a walk across the doubling of an edge

Osin (math/0411039v3, §9), Lemma 9.4, Case 1: the pocket corners at a touch vertex are thickened by
doubling an edge (`OsinPocketTouchCornerThickening`).  The pocket walk passes to the doubled map by
the dart embedding, and the faces that were off its side stay off it.

The argument projects the doubled map back.  The two new darts go to the doubled dart and every old
dart to itself (`project`).  Faces project consistently (`faceOf_project_eq`): the digon and the
image of the doubled face both go to the doubled face.  So every face-class step of the doubled
walk projects to a face-class chain of the old walk (`eqvGen_project`), and a face whose image is
on the new side was on the old side (`not_mem_sideFaces_faceImage`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.PocketTouchCorner

open EdgeInsertion SimpleClosedWalkSides

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The projection of the darts of an edge insertion: the new darts go to `d₀`. -/
def project {M : CombMap.{v}} (d₀ : M.Dart) : EdgeInsertion.Dart M → M.Dart
  | none => d₀
  | some none => d₀
  | some (some d) => d

section Sides

variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- A face of the doubled map is the image of the face of the projected dart, or it is the digon
and the projected dart lies on the doubled face. -/
theorem faceOf_project (x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart) :
    (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
        FaceEdgeDoubling.faceImage Delta f j hlen
          (Delta.toCombMap.faceOf (project (FaceEdgeDoubling.dart Delta f j) x)) ∨
      ((FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
          FaceEdgeDoubling.digon Delta f j hlen ∧
        Delta.toCombMap.faceOf (project (FaceEdgeDoubling.dart Delta f j) x) = f) := by
  rcases x with _ | (_ | d)
  · exact Or.inr ⟨FaceEdgeDoubling.faceOf_none_digon Delta f j hlen,
      FaceEdgeDoubling.dart_face Delta f j⟩
  · refine Or.inl ?_
    show _ = FaceEdgeDoubling.faceImage Delta f j hlen
      (Delta.toCombMap.faceOf (FaceEdgeDoubling.dart Delta f j))
    rw [FaceEdgeDoubling.dart_face Delta f j, FaceEdgeDoubling.faceImage_self]
    exact FaceEdgeDoubling.faceOf_some_none_cellFace Delta f j hlen
  · by_cases hd : d = FaceEdgeDoubling.dart Delta f j
    · subst hd
      exact Or.inr ⟨FaceEdgeDoubling.faceOf_embed_dart_digon Delta f j hlen,
        FaceEdgeDoubling.dart_face Delta f j⟩
    · exact Or.inl (CellEdgeThickening.faceOf_embed_eq_faceImage Delta f j hlen hd)

/-- **Faces project consistently.** -/
theorem faceOf_project_eq {x y : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (h : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
      (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf y) :
    Delta.toCombMap.faceOf (project (FaceEdgeDoubling.dart Delta f j) x) =
      Delta.toCombMap.faceOf (project (FaceEdgeDoubling.dart Delta f j) y) := by
  rcases faceOf_project Delta f j hlen hf x with hx | ⟨hx, hx'⟩ <;>
    rcases faceOf_project Delta f j hlen hf y with hy | ⟨hy, hy'⟩
  · exact FaceEdgeDoubling.faceImage_injective Delta f j hlen (hx.symm.trans (h.trans hy))
  · exact (FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen _ (hx.symm.trans (h.trans hy))).elim
  · exact (FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen _
      (hy.symm.trans (h.symm.trans hx))).elim
  · exact hx'.trans hy'.symm

/-- An old dart keeps an edge of the embedded walk exactly when it keeps an edge of the walk. -/
theorem walkKeep_embedding {walk : List Delta.toCombMap.Dart} (d : Delta.toCombMap.Dart) :
    walkKeep (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap
        (walk.map (FaceEdgeDoubling.embedding Delta f j hlen hf).darts)
        ((FaceEdgeDoubling.embedding Delta f j hlen hf).darts d) ↔
      walkKeep Delta.toCombMap walk d := by
  unfold walkKeep
  rw [(FaceEdgeDoubling.embedding Delta f j hlen hf).alpha,
    List.mem_map_of_injective (FaceEdgeDoubling.embedding Delta f j hlen hf).darts.injective,
    List.mem_map_of_injective (FaceEdgeDoubling.embedding Delta f j hlen hf).darts.injective]

/-- **A face-class chain of the embedded walk projects to a face-class chain of the walk.** -/
theorem eqvGen_project {walk : List Delta.toCombMap.Dart}
    {x y : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap
      (walkKeep (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap
        (walk.map (FaceEdgeDoubling.embedding Delta f j hlen hf).darts))) x y) :
    Relation.EqvGen (CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap walk))
      (project (FaceEdgeDoubling.dart Delta f j) x) (project (FaceEdgeDoubling.dart Delta f j) y) := by
  induction h with
  | rel x₁ x₂ hstep =>
      rcases hstep with rfl | ⟨hk, rfl⟩
      · refine eqvGen_faceClass_of_sameCycle Delta.toCombMap _
          ((Delta.toCombMap.faceOf_eq_iff _ _).mp (faceOf_project_eq Delta f j hlen hf ?_))
        exact ((FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf_eq_iff _ _).mpr
          ⟨1, by rw [zpow_one]⟩
      · rcases x₁ with _ | (_ | d)
        · exact .refl _
        · exact .refl _
        · exact .rel _ _ (Or.inr ⟨fun hkd => hk ((walkKeep_embedding Delta f j hlen hf d).mpr hkd),
            rfl⟩)
  | refl x₁ => exact .refl _
  | symm x₁ x₂ _ ih => exact .symm _ _ ih
  | trans x₁ x₂ x₃ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- **A face on the side of the embedded walk projects to a face on the side of the walk.** -/
theorem mem_sideFaces_project {walk : List Delta.toCombMap.Dart}
    {x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hx : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x ∈
      sideFaces (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap
        (walk.map (FaceEdgeDoubling.embedding Delta f j hlen hf).darts)) :
    Delta.toCombMap.faceOf (project (FaceEdgeDoubling.dart Delta f j) x) ∈
      sideFaces Delta.toCombMap walk := by
  obtain ⟨d', hd', hch⟩ := (mem_sideFaces_iff _ _ x).mp hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
  exact (mem_sideFaces_iff _ _ _).mpr ⟨d, hd, eqvGen_project Delta f j hlen hf hch⟩

/-- **A face off the side stays off the side**, for a face other than the doubled one. -/
theorem not_mem_sideFaces_faceImage {walk : List Delta.toCombMap.Dart}
    {g : Delta.toCombMap.Face} (hg : g ≠ f) (hside : g ∉ sideFaces Delta.toCombMap walk) :
    FaceEdgeDoubling.faceImage Delta f j hlen g ∉
      sideFaces (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap
        (walk.map (FaceEdgeDoubling.embedding Delta f j hlen hf).darts) := by
  intro hmem
  obtain ⟨o, ho⟩ : ∃ o, Delta.toCombMap.faceOf o = g :=
    ⟨(Delta.faceBoundary g).darts.head (Delta.faceBoundary g).nonempty,
      ((Delta.faceBoundary g).mem_iff _).mp (List.head_mem _)⟩
  have hne : o ≠ FaceEdgeDoubling.dart Delta f j := fun h =>
    hg (by rw [← ho, h, FaceEdgeDoubling.dart_face Delta f j])
  have hface : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf
      ((FaceEdgeDoubling.embedding Delta f j hlen hf).darts o) =
      FaceEdgeDoubling.faceImage Delta f j hlen g := by
    rw [← ho]
    exact CellEdgeThickening.faceOf_embed_eq_faceImage Delta f j hlen hne
  rw [← hface] at hmem
  exact hside (by rw [← ho]; exact mem_sideFaces_project Delta f j hlen hf hmem)

end Sides

end GroupApproximation.GGT.VanKampen.PocketTouchCorner

#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.faceOf_project
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.faceOf_project_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.walkKeep_embedding
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.eqvGen_project
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.mem_sideFaces_project
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.not_mem_sideFaces_faceImage
