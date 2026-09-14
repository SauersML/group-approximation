import GroupApproximation.GGT.VanKampen.BridgeComponentValue
import GroupApproximation.GGT.VanKampen.PlanarVanKampenDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# A disc diagram on a planar invariant piece of a labelled map

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Gluing a copy of a pocket back into a
diagram can split the glued map into several components (`OsinPocketFullArcLakeGlueModel`); the
component of the exterior, when planar, is a disc diagram with the boundary word of the diagram and
fewer relator cells when a relator face lies elsewhere.  This file builds that disc diagram.

Let `S` be a set of darts closed under edge reversal and vertex rotation, with planar restricted map
`M.restrict S hα hσ` (`CombMapInvariantRestrict`).  A face of the restriction is a face of `M`
(`restrictFace`, injective), and every dart on it lies in `S`, so a traversal of a face of `M` lifts to
a traversal of the face of the restriction (`restrictFaceBoundary`, with the same darts on values,
`restrictFaceBoundary_darts`).  With labels, relator faces and a dart `o ∈ S` giving the outer face,
`DiscDiagram.ofPlanar` (`PlanarVanKampenDiagram`) makes the restriction a disc diagram
(`DiscDiagram.ofPlanarRestrict`).  Its relator cells are the relator faces met by `S`
(`ofPlanarRestrict_rCellCount`, and `ofPlanarRestrict_rCellCount_of_forall` when all are), and it reads
the reverse-inverse of the face of `o` (`ofPlanarRestrict_boundaryWord`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC
open scoped Classical

universe u w v

namespace CombMap

section Faces

variable (M : CombMap.{v}) (S : M.Dart → Prop) (hα : ∀ x, S (M.alpha x) ↔ S x)
  (hσ : ∀ x, S (M.sigma x) ↔ S x)

/-- Two darts of the restriction share a face exactly when their values share a face of the map. -/
theorem restrict_sameCycle_iff (a b : (M.restrict S hα hσ).Dart) :
    (M.restrict S hα hσ).facePerm.SameCycle a b ↔ M.facePerm.SameCycle a.1 b.1 :=
  (Iff.of_eq (congrArg (fun p => Equiv.Perm.SameCycle p a b) (M.restrict_facePerm_eq S hα hσ))).trans
    Equiv.Perm.sameCycle_subtypePerm

/-- **A face of the restriction as a face of the map.** -/
noncomputable def restrictFace : (M.restrict S hα hσ).Face → M.Face :=
  Quotient.map' Subtype.val fun a b h => (M.restrict_sameCycle_iff S hα hσ a b).mp h

theorem restrictFace_faceOf (x : (M.restrict S hα hσ).Dart) :
    M.restrictFace S hα hσ ((M.restrict S hα hσ).faceOf x) = M.faceOf x.1 :=
  rfl

theorem restrictFace_injective : Function.Injective (M.restrictFace S hα hσ) := by
  intro F G h
  obtain ⟨a, rfl⟩ := Quotient.exists_rep F
  obtain ⟨b, rfl⟩ := Quotient.exists_rep G
  exact ((M.restrict S hα hσ).faceOf_eq_iff a b).mpr
    ((M.restrict_sameCycle_iff S hα hσ a b).mpr ((M.faceOf_eq_iff a.1 b.1).mp h))

include hα hσ in
/-- Every dart on the face of a dart of `S` lies in `S`. -/
theorem mem_of_faceOf_eq {x d : M.Dart} (hx : S x) (hd : M.faceOf d = M.faceOf x) : S d :=
  (iff_of_sameCycle M.facePerm S (M.facePerm_invariant S hα hσ)
    ((M.faceOf_eq_iff d x).mp hd)).mpr hx

/-- Every dart on the image of a face of the restriction lies in `S`. -/
theorem mem_of_faceOf_eq_restrictFace (F : (M.restrict S hα hσ).Face) {d : M.Dart}
    (hd : M.faceOf d = M.restrictFace S hα hσ F) : S d := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep F
  exact M.mem_of_faceOf_eq S hα hσ a.2 hd

/-- The traversal of the image of a face of the restriction, as darts of the restriction. -/
noncomputable def liftTraversal (faceBoundary : ∀ f, FaceBoundary M f)
    (F : (M.restrict S hα hσ).Face) : List (M.restrict S hα hσ).Dart :=
  (faceBoundary (M.restrictFace S hα hσ F)).darts.pmap Subtype.mk fun d hd =>
    M.mem_of_faceOf_eq_restrictFace S hα hσ F (((faceBoundary _).mem_iff d).mp hd)

theorem liftTraversal_map_val (faceBoundary : ∀ f, FaceBoundary M f)
    (F : (M.restrict S hα hσ).Face) :
    (M.liftTraversal S hα hσ faceBoundary F).map Subtype.val =
      (faceBoundary (M.restrictFace S hα hσ F)).darts :=
  (List.map_pmap _).trans ((List.pmap_eq_map _).trans (List.map_id' _))

theorem isFaceCycle_liftTraversal (faceBoundary : ∀ f, FaceBoundary M f)
    (F : (M.restrict S hα hσ).Face) :
    (M.restrict S hα hσ).IsFaceCycle (M.liftTraversal S hα hσ faceBoundary F) := by
  have h := (faceBoundary (M.restrictFace S hα hσ F)).isFaceCycle
  rw [← M.liftTraversal_map_val S hα hσ faceBoundary F] at h
  exact BridgeComponent.isFaceCycle_of_val S hα hσ h

theorem mem_liftTraversal_iff (faceBoundary : ∀ f, FaceBoundary M f)
    (F : (M.restrict S hα hσ).Face) (d : (M.restrict S hα hσ).Dart) :
    d ∈ M.liftTraversal S hα hσ faceBoundary F ↔ (M.restrict S hα hσ).faceOf d = F := by
  have hval : d ∈ M.liftTraversal S hα hσ faceBoundary F ↔
      d.1 ∈ (faceBoundary (M.restrictFace S hα hσ F)).darts := by
    rw [← M.liftTraversal_map_val S hα hσ faceBoundary F]
    exact ⟨fun h => List.mem_map_of_mem h, fun h => by
      obtain ⟨e, he, hed⟩ := List.mem_map.mp h
      exact (Subtype.ext hed : e = d) ▸ he⟩
  rw [hval, (faceBoundary (M.restrictFace S hα hσ F)).mem_iff d.1]
  exact ⟨fun h => M.restrictFace_injective S hα hσ
      (show M.restrictFace S hα hσ ((M.restrict S hα hσ).faceOf d) = M.restrictFace S hα hσ F
        from h),
    fun h => by subst h; rfl⟩

/-- **A traversal of every face of the restriction**, lifted from the traversal of its image. -/
noncomputable def restrictFaceBoundary (faceBoundary : ∀ f, FaceBoundary M f)
    (F : (M.restrict S hα hσ).Face) : FaceBoundary (M.restrict S hα hσ) F where
  darts := M.liftTraversal S hα hσ faceBoundary F
  nonempty := (M.isFaceCycle_liftTraversal S hα hσ faceBoundary F).ne_nil
  nodup := (M.isFaceCycle_liftTraversal S hα hσ faceBoundary F).nodup
  mem_iff := M.mem_liftTraversal_iff S hα hσ faceBoundary F
  chain := (M.isFaceCycle_liftTraversal S hα hσ faceBoundary F).chain
  closes := (M.isFaceCycle_liftTraversal S hα hσ faceBoundary F).closes
  length_eq_degree :=
    (M.isFaceCycle_liftTraversal S hα hσ faceBoundary F).length_eq.trans
      (congrArg (M.restrict S hα hσ).faceDegree
        ((M.mem_liftTraversal_iff S hα hσ faceBoundary F _).mp
          (List.head_mem (M.isFaceCycle_liftTraversal S hα hσ faceBoundary F).ne_nil)))

/-- The lifted traversal has the darts of the traversal of the image, on values. -/
theorem restrictFaceBoundary_darts (faceBoundary : ∀ f, FaceBoundary M f)
    (F : (M.restrict S hα hσ).Face) :
    (M.restrictFaceBoundary S hα hσ faceBoundary F).darts.map Subtype.val =
      (faceBoundary (M.restrictFace S hα hσ F)).darts :=
  M.liftTraversal_map_val S hα hσ faceBoundary F

/-- The lifted traversal reads the word of the traversal of the image. -/
theorem restrictFaceBoundary_word {β : Type*} (faceBoundary : ∀ f, FaceBoundary M f)
    (label : M.Dart → β) (F : (M.restrict S hα hσ).Face) :
    (M.restrictFaceBoundary S hα hσ faceBoundary F).darts.map (fun x => label x.1) =
      (faceBoundary (M.restrictFace S hα hσ F)).darts.map label :=
  (List.map_map (g := label) (f := Subtype.val)
    (l := (M.restrictFaceBoundary S hα hσ faceBoundary F).darts)).symm.trans
    (congrArg (List.map label) (M.restrictFaceBoundary_darts S hα hσ faceBoundary F))

/-- The relator faces of the map, on the restriction. -/
noncomputable def restrictRelFaces (relFaces : Finset M.Face) :
    Finset (M.restrict S hα hσ).Face :=
  Finset.univ.filter fun F => M.restrictFace S hα hσ F ∈ relFaces

theorem image_restrictRelFaces (relFaces : Finset M.Face) :
    (M.restrictRelFaces S hα hσ relFaces).image (M.restrictFace S hα hσ) =
      relFaces.filter fun f => ∃ d, S d ∧ M.faceOf d = f := by
  ext f
  rw [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨F, hF, rfl⟩
    obtain ⟨a, rfl⟩ := Quotient.exists_rep F
    exact ⟨(Finset.mem_filter.mp hF).2, a.1, a.2, rfl⟩
  · rintro ⟨hf, d, hd, rfl⟩
    exact ⟨(M.restrict S hα hσ).faceOf ⟨d, hd⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩,
      rfl⟩

/-- The relator faces on the restriction are the relator faces met by `S`. -/
theorem card_restrictRelFaces (relFaces : Finset M.Face) :
    (M.restrictRelFaces S hα hσ relFaces).card =
      (relFaces.filter fun f => ∃ d, S d ∧ M.faceOf d = f).card := by
  rw [← M.image_restrictRelFaces S hα hσ relFaces]
  exact (Finset.card_image_of_injective _ (M.restrictFace_injective S hα hσ)).symm

theorem restrictRelFaces_outer_not_mem (relFaces : Finset M.Face) (o : M.Dart) (ho : S o)
    (houter : M.faceOf o ∉ relFaces) :
    (M.restrict S hα hσ).faceOf ⟨o, ho⟩ ∉ M.restrictRelFaces S hα hσ relFaces :=
  fun h => houter (Finset.mem_filter.mp h).2

theorem restrictRelFaces_word {β : Type*} (faceBoundary : ∀ f, FaceBoundary M f)
    (label : M.Dart → β) (relFaces : Finset M.Face) {T : Set (List β)}
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ T) :
    ∀ F ∈ M.restrictRelFaces S hα hσ relFaces,
      (M.restrictFaceBoundary S hα hσ faceBoundary F).darts.map (fun x => label x.1) ∈ T := by
  intro F hF
  rw [M.restrictFaceBoundary_word S hα hσ faceBoundary label F]
  exact hword _ (Finset.mem_filter.mp hF).2

end Faces

section Triv

variable {G : Type u} [Group G] {Lambda : Type w}
variable (M : CombMap.{v}) (S : M.Dart → Prop) (hα : ∀ x, S (M.alpha x) ↔ S x)
  (hσ : ∀ x, S (M.sigma x) ↔ S x)

theorem restrictRelFaces_triv (faceBoundary : ∀ f, FaceBoundary M f)
    (label : M.Dart → RelLetter G Lambda) (relFaces : Finset M.Face) (o : M.Dart) (ho : S o)
    (htriv : ∀ d, S d → M.faceOf d ≠ M.faceOf o → M.faceOf d ∉ relFaces →
      RelLetter.listVal ((faceBoundary (M.faceOf d)).darts.map label) = 1) :
    ∀ F, F ≠ (M.restrict S hα hσ).faceOf ⟨o, ho⟩ → F ∉ M.restrictRelFaces S hα hσ relFaces →
      RelLetter.listVal ((M.restrictFaceBoundary S hα hσ faceBoundary F).darts.map
        (fun x => label x.1)) = 1 := by
  intro F hF hnot
  obtain ⟨a, rfl⟩ := Quotient.exists_rep F
  rw [M.restrictFaceBoundary_word S hα hσ faceBoundary label]
  exact htriv a.1 a.2
    (fun h => hF (M.restrictFace_injective S hα hσ
      (show M.restrictFace S hα hσ ((M.restrict S hα hσ).faceOf a) =
        M.restrictFace S hα hσ ((M.restrict S hα hσ).faceOf ⟨o, ho⟩) from h)))
    (fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))

end Triv

end CombMap

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The disc diagram on a planar invariant piece of a labelled map.**  A set of darts closed under
edge reversal and vertex rotation, with planar restricted map, labels, relator faces reading words of
`W`, freely trivial remaining faces on the piece, and a dart `o` of the piece giving the outer face. -/
noncomputable def DiscDiagram.ofPlanarRestrict {W : Set (List (RelLetter G Lambda))}
    (M : CombMap.{v}) (S : M.Dart → Prop) (hα : ∀ x, S (M.alpha x) ↔ S x)
    (hσ : ∀ x, S (M.sigma x) ↔ S x) (hplanar : (M.restrict S hα hσ).IsPlanar)
    (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d))
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face) (o : M.Dart) (ho : S o)
    (houter : M.faceOf o ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W)
    (htriv : ∀ d, S d → M.faceOf d ≠ M.faceOf o → M.faceOf d ∉ relFaces →
      RelLetter.listVal ((faceBoundary (M.faceOf d)).darts.map label) = 1) :
    DiscDiagram.{u, w, v} W :=
  DiscDiagram.ofPlanar (M.restrict S hα hσ) hplanar (fun x => label x.1)
    (fun x => label_alpha x.1) ((M.restrict S hα hσ).faceOf ⟨o, ho⟩)
    (M.restrictFaceBoundary S hα hσ faceBoundary) (M.restrictRelFaces S hα hσ relFaces)
    (M.restrictRelFaces_outer_not_mem S hα hσ relFaces o ho houter)
    (M.restrictRelFaces_word S hα hσ faceBoundary label relFaces hword)
    (M.restrictRelFaces_triv S hα hσ faceBoundary label relFaces o ho htriv)

/-- **The relator cells of the piece are the relator faces it meets.** -/
theorem DiscDiagram.ofPlanarRestrict_rCellCount {W : Set (List (RelLetter G Lambda))}
    (M : CombMap.{v}) (S : M.Dart → Prop) (hα : ∀ x, S (M.alpha x) ↔ S x)
    (hσ : ∀ x, S (M.sigma x) ↔ S x) (hplanar : (M.restrict S hα hσ).IsPlanar)
    (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d))
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face) (o : M.Dart) (ho : S o)
    (houter : M.faceOf o ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W)
    (htriv : ∀ d, S d → M.faceOf d ≠ M.faceOf o → M.faceOf d ∉ relFaces →
      RelLetter.listVal ((faceBoundary (M.faceOf d)).darts.map label) = 1) :
    (DiscDiagram.ofPlanarRestrict (W := W) M S hα hσ hplanar label label_alpha faceBoundary
      relFaces o ho houter hword htriv).rCellCount =
        (relFaces.filter fun f => ∃ d, S d ∧ M.faceOf d = f).card :=
  (DiscDiagram.ofPlanar_rCellCount (W := W) (M.restrict S hα hσ) hplanar (fun x => label x.1)
    (fun x => label_alpha x.1) ((M.restrict S hα hσ).faceOf ⟨o, ho⟩)
    (M.restrictFaceBoundary S hα hσ faceBoundary) (M.restrictRelFaces S hα hσ relFaces)
    (M.restrictRelFaces_outer_not_mem S hα hσ relFaces o ho houter)
    (M.restrictRelFaces_word S hα hσ faceBoundary label relFaces hword)
    (M.restrictRelFaces_triv S hα hσ faceBoundary label relFaces o ho htriv)).trans
    (M.card_restrictRelFaces S hα hσ relFaces)

/-- **A piece meeting every relator face has one relator cell for each.** -/
theorem DiscDiagram.ofPlanarRestrict_rCellCount_of_forall {W : Set (List (RelLetter G Lambda))}
    (M : CombMap.{v}) (S : M.Dart → Prop) (hα : ∀ x, S (M.alpha x) ↔ S x)
    (hσ : ∀ x, S (M.sigma x) ↔ S x) (hplanar : (M.restrict S hα hσ).IsPlanar)
    (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d))
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face) (o : M.Dart) (ho : S o)
    (houter : M.faceOf o ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W)
    (htriv : ∀ d, S d → M.faceOf d ≠ M.faceOf o → M.faceOf d ∉ relFaces →
      RelLetter.listVal ((faceBoundary (M.faceOf d)).darts.map label) = 1)
    (hall : ∀ f ∈ relFaces, ∃ d, S d ∧ M.faceOf d = f) :
    (DiscDiagram.ofPlanarRestrict (W := W) M S hα hσ hplanar label label_alpha faceBoundary
      relFaces o ho houter hword htriv).rCellCount = relFaces.card :=
  (DiscDiagram.ofPlanarRestrict_rCellCount (W := W) M S hα hσ hplanar label label_alpha
    faceBoundary relFaces o ho houter hword htriv).trans
    (congrArg Finset.card (Finset.filter_true_of_mem hall))

/-- **The piece reads the reverse-inverse of the face of `o`.** -/
theorem DiscDiagram.ofPlanarRestrict_boundaryWord {W : Set (List (RelLetter G Lambda))}
    (M : CombMap.{v}) (S : M.Dart → Prop) (hα : ∀ x, S (M.alpha x) ↔ S x)
    (hσ : ∀ x, S (M.sigma x) ↔ S x) (hplanar : (M.restrict S hα hσ).IsPlanar)
    (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d))
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face) (o : M.Dart) (ho : S o)
    (houter : M.faceOf o ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W)
    (htriv : ∀ d, S d → M.faceOf d ≠ M.faceOf o → M.faceOf d ∉ relFaces →
      RelLetter.listVal ((faceBoundary (M.faceOf d)).darts.map label) = 1) :
    (DiscDiagram.ofPlanarRestrict (W := W) M S hα hσ hplanar label label_alpha faceBoundary
      relFaces o ho houter hword htriv).boundaryWord =
        RelWord.revInv ((faceBoundary (M.faceOf o)).darts.map label) :=
  congrArg RelWord.revInv
    (M.restrictFaceBoundary_word S hα hσ faceBoundary label ((M.restrict S hα hσ).faceOf ⟨o, ho⟩))

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.restrictFace_injective
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.restrictFaceBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.restrictFaceBoundary_darts
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.card_restrictRelFaces
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.ofPlanarRestrict
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.ofPlanarRestrict_rCellCount
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.ofPlanarRestrict_rCellCount_of_forall
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.ofPlanarRestrict_boundaryWord
