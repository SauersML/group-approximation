import GroupApproximation.GGT.VanKampen.CombMapEdgeLabels
import GroupApproximation.GGT.VanKampen.CombMapEdgePlanarity
import GroupApproximation.GGT.VanKampen.SurgeryCellMap
import GroupApproximation.GGT.VanKampen.FaceBoundaryRotation
import GroupApproximation.Meta.AxiomGuard

/-!
# Doubling one edge of a face into a G-cell digon

Osin's Appendix (arXiv:math/0411039v3, §9) works with diagrams in which relator cells never
share an edge with each other or with the exterior: a 0-refinement separates them.  In an
arbitrary diagram they can, and the maximality argument of Lemma 9.4 needs the separating
G-cell explicitly.  This file constructs it.

Let `f` be an inner face (a relator face or a G-face) and `w_j` a dart of its traversal
`w_0 … w_{n-1}`.  Rebase the traversal at `w_j` and insert an edge across `f` between the
corner before `w_j` and the corner after it (`EdgeInsertion.splitMap`), labelled by the
label of `w_j`.  The inserted edge closes a digon `none, w_j`, a G-face of value one, and
the rest of `f` reads `w_0 … w_{j-1}, new, w_{j+1} … w_{n-1}`: the same word, with the new
dart in the place of `w_j` (`boundary_cellFace_darts`).  The stored traversal of that face
is rotated back to the original base point, so a relator cell on `f` keeps its word
literally.  Every other face keeps its darts.

The result is O-equivalent, keeps reducedness and label legality, and is planar
(`EdgeInsertion.planar`).
-/

namespace GroupApproximation.GGT.VanKampen.FaceEdgeDoubling

open HullSC EdgeInsertion Surgery
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length)

/-- The traversal of `f` rebased at the doubled dart. -/
abbrev rebased : FaceBoundary Delta.toCombMap f := (Delta.faceBoundary f).rotate j.val

theorem rebased_length :
    (rebased Delta f j).darts.length = (Delta.faceBoundary f).darts.length :=
  List.length_rotate _ _

/-- The corner after the doubled dart. -/
def second : Fin (rebased Delta f j).darts.length :=
  ⟨1, by rw [rebased_length]; exact hlen⟩

/-- The doubled dart `w_j`. -/
def dart : Delta.toCombMap.Dart := firstCorner Delta.toCombMap (rebased Delta f j)

theorem firstCorner_eq_head {M : CombMap.{v}} {g : M.Face} (B : FaceBoundary M g) :
    firstCorner M B = B.darts.head B.nonempty := by
  simp only [firstCorner, List.get_eq_getElem, List.head_eq_getElem]

theorem darts_eq_cons {M : CombMap.{v}} {g : M.Face} (B : FaceBoundary M g) :
    B.darts = firstCorner M B :: B.darts.drop 1 := by
  rw [firstCorner_eq_head, List.drop_one]
  exact (List.cons_head_tail B.nonempty).symm

theorem rebased_eq_cons :
    (rebased Delta f j).darts = dart Delta f j :: (rebased Delta f j).darts.drop 1 :=
  darts_eq_cons (rebased Delta f j)

theorem take_one_rebased : (rebased Delta f j).darts.take 1 = [dart Delta f j] := by
  rw [rebased_eq_cons]
  rfl

theorem dart_eq_get : dart Delta f j = (Delta.faceBoundary f).darts.get j := by
  rw [dart, firstCorner_eq_head]
  change ((Delta.faceBoundary f).darts.rotate j.val).head _ = _
  rw [List.head_eq_getElem, List.getElem_rotate, List.get_eq_getElem]
  simp only [Nat.zero_add, Nat.mod_eq_of_lt j.isLt]

/-- The doubled map. -/
noncomputable abbrev map : CombMap.{v} :=
  splitMap Delta.toCombMap (rebased Delta f j) (second Delta f j hlen)

/-- A retained face other than `f`. -/
noncomputable abbrev keep (g : Delta.toCombMap.Face) : (map Delta f j hlen).Face :=
  keptFace Delta.toCombMap (firstCorner Delta.toCombMap (rebased Delta f j))
    (secondCorner Delta.toCombMap (rebased Delta f j) (second Delta f j hlen)) g

/-- The new digon. -/
noncomputable abbrev digon : (map Delta f j hlen).Face :=
  prefixFace Delta.toCombMap (rebased Delta f j) (second Delta f j hlen)

/-- The face `f`, with the new dart in the place of `w_j`. -/
noncomputable abbrev cellFace : (map Delta f j hlen).Face :=
  suffixFace Delta.toCombMap (rebased Delta f j) (second Delta f j hlen)

/-- Where an old face goes. -/
noncomputable def faceImage (g : Delta.toCombMap.Face) : (map Delta f j hlen).Face :=
  if g = f then cellFace Delta f j hlen else keep Delta f j hlen g

theorem faceImage_self : faceImage Delta f j hlen f = cellFace Delta f j hlen := if_pos rfl

theorem faceImage_of_ne {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    faceImage Delta f j hlen g = keep Delta f j hlen g := if_neg hg

theorem keep_ne_cellFace {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    keep Delta f j hlen g ≠ cellFace Delta f j hlen :=
  keptFace_ne_suffixFace Delta.toCombMap (rebased Delta f j) (second Delta f j hlen) g hg

theorem keep_ne_digon {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    keep Delta f j hlen g ≠ digon Delta f j hlen :=
  keptFace_ne_prefixFace Delta.toCombMap (rebased Delta f j) (second Delta f j hlen) g hg

theorem digon_ne_cellFace : digon Delta f j hlen ≠ cellFace Delta f j hlen :=
  prefixFace_ne_suffixFace Delta.toCombMap (rebased Delta f j) (second Delta f j hlen)

theorem keep_injective : Function.Injective (keep Delta f j hlen) :=
  keptFace_injective Delta.toCombMap _ _
    (corners_face_eq Delta.toCombMap (rebased Delta f j) (second Delta f j hlen))

theorem faceImage_injective : Function.Injective (faceImage Delta f j hlen) := by
  intro g h heq
  by_cases hg : g = f
  · by_cases hh : h = f
    · exact hg.trans hh.symm
    · rw [hg, faceImage_self, faceImage_of_ne Delta f j hlen hh] at heq
      exact (keep_ne_cellFace Delta f j hlen hh heq.symm).elim
  · by_cases hh : h = f
    · rw [hh, faceImage_self, faceImage_of_ne Delta f j hlen hg] at heq
      exact (keep_ne_cellFace Delta f j hlen hg heq).elim
    · rw [faceImage_of_ne Delta f j hlen hg, faceImage_of_ne Delta f j hlen hh] at heq
      exact keep_injective Delta f j hlen heq

theorem faceImage_ne_digon (g : Delta.toCombMap.Face) :
    faceImage Delta f j hlen g ≠ digon Delta f j hlen := by
  by_cases hg : g = f
  · rw [hg, faceImage_self]
    exact (digon_ne_cellFace Delta f j hlen).symm
  · rw [faceImage_of_ne Delta f j hlen hg]
    exact keep_ne_digon Delta f j hlen hg

/-- The labels: the new dart carries the label of `w_j`. -/
noncomputable abbrev label : (map Delta f j hlen).Dart → RelLetter G Lambda :=
  insertLabel Delta.toCombMap Delta.label (Delta.label (dart Delta f j))

/-- Every face traversal; the one of `f` is rotated back to its old base point. -/
noncomputable def boundary (F : (map Delta f j hlen).Face) : FaceBoundary (map Delta f j hlen) F :=
  (allFaceBoundary Delta.toCombMap (rebased Delta f j) Delta.faceBoundary
    (second Delta f j hlen) F).rotate
      (if F = cellFace Delta f j hlen then (Delta.faceBoundary f).darts.length - j.val else 0)

theorem boundary_darts (F : (map Delta f j hlen).Face) :
    (boundary Delta f j hlen F).darts =
      (allFaceBoundary Delta.toCombMap (rebased Delta f j) Delta.faceBoundary
        (second Delta f j hlen) F).darts.rotate
          (if F = cellFace Delta f j hlen then (Delta.faceBoundary f).darts.length - j.val
            else 0) := rfl

theorem boundary_kept {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    (boundary Delta f j hlen (keep Delta f j hlen g)).darts =
      (Delta.faceBoundary g).darts.map (embed Delta.toCombMap) := by
  rw [boundary_darts, if_neg (keep_ne_cellFace Delta f j hlen hg), List.rotate_zero]
  exact allFaceBoundary_kept Delta.toCombMap (rebased Delta f j) Delta.faceBoundary
    (second Delta f j hlen) g hg

theorem boundary_digon :
    (boundary Delta f j hlen (digon Delta f j hlen)).darts =
      [none, embed Delta.toCombMap (dart Delta f j)] := by
  rw [boundary_darts, if_neg (digon_ne_cellFace Delta f j hlen), List.rotate_zero,
    allFaceBoundary_prefix]
  change none :: ((rebased Delta f j).darts.take 1).map (embed Delta.toCombMap) = _
  rw [take_one_rebased]
  rfl

theorem boundary_kept_word {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    (boundary Delta f j hlen (keep Delta f j hlen g)).darts.map (label Delta f j hlen) =
      (Delta.faceBoundary g).darts.map Delta.label := by
  rw [boundary_darts, if_neg (keep_ne_cellFace Delta f j hlen hg), List.rotate_zero]
  exact split_kept_word Delta.toCombMap (rebased Delta f j) Delta.faceBoundary
    (second Delta f j hlen) g hg Delta.label (Delta.label (dart Delta f j))

theorem prefix_value :
    (Delta.label (dart Delta f j)).val =
      RelLetter.listVal (((rebased Delta f j).darts.take (second Delta f j hlen).val).map
        Delta.label) := by
  change _ = RelLetter.listVal (((rebased Delta f j).darts.take 1).map Delta.label)
  rw [take_one_rebased]
  change _ = ([Delta.label (dart Delta f j)].map RelLetter.val).prod
  rw [List.map_singleton, List.prod_singleton]

theorem boundary_digon_value :
    RelLetter.listVal ((boundary Delta f j hlen (digon Delta f j hlen)).darts.map
      (label Delta f j hlen)) = 1 := by
  rw [boundary_darts, if_neg (digon_ne_cellFace Delta f j hlen), List.rotate_zero]
  exact split_prefix_null Delta.toCombMap (rebased Delta f j) Delta.faceBoundary
    (second Delta f j hlen) Delta.label (Delta.label (dart Delta f j)) (prefix_value Delta f j hlen)

/-- The face of `f` reads the old word of `f`. -/
theorem boundary_cellFace_word :
    (boundary Delta f j hlen (cellFace Delta f j hlen)).darts.map (label Delta f j hlen) =
      (Delta.faceBoundary f).darts.map Delta.label := by
  rw [boundary_darts, if_pos rfl, List.map_rotate]
  have hsw := split_suffix_word Delta.toCombMap (rebased Delta f j) Delta.faceBoundary
    (second Delta f j hlen) Delta.label (Delta.label (dart Delta f j))
  refine (congrArg (fun l : List (RelLetter G Lambda) =>
    l.rotate ((Delta.faceBoundary f).darts.length - j.val)) hsw).trans ?_
  have hcons : Delta.label (dart Delta f j) ::
      ((rebased Delta f j).darts.drop (second Delta f j hlen).val).map Delta.label =
        (rebased Delta f j).darts.map Delta.label := by
    change Delta.label (dart Delta f j) :: ((rebased Delta f j).darts.drop 1).map Delta.label = _
    conv_rhs => rw [rebased_eq_cons Delta f j]
    rfl
  rw [hcons]
  change (((Delta.faceBoundary f).darts.rotate j.val).map Delta.label).rotate
    ((Delta.faceBoundary f).darts.length - j.val) = _
  rw [List.map_rotate, List.rotate_rotate, Nat.add_sub_of_le (Nat.le_of_lt j.isLt)]
  simpa only [List.length_map] using List.rotate_length ((Delta.faceBoundary f).darts.map Delta.label)

/-- The dart map onto the face of `f`: `w_j` goes to the new dart. -/
noncomputable def dartImage (d : Delta.toCombMap.Dart) : (map Delta f j hlen).Dart :=
  if d = dart Delta f j then some none else embed Delta.toCombMap d

/-- **The face of `f` is the old traversal with the new dart in the place of `w_j`.** -/
theorem boundary_cellFace_darts :
    (boundary Delta f j hlen (cellFace Delta f j hlen)).darts =
      (Delta.faceBoundary f).darts.map (dartImage Delta f j hlen) := by
  rw [boundary_darts, if_pos rfl, allFaceBoundary_suffix]
  have hnodup : (rebased Delta f j).darts.Nodup := (rebased Delta f j).nodup
  have hsuffix : suffixDarts Delta.toCombMap (rebased Delta f j) (second Delta f j hlen) =
      (rebased Delta f j).darts.map (dartImage Delta f j hlen) := by
    change some none :: ((rebased Delta f j).darts.drop 1).map (embed Delta.toCombMap) = _
    have hnd := hnodup
    rw [rebased_eq_cons Delta f j] at hnd
    conv_rhs => rw [rebased_eq_cons Delta f j]
    rw [List.map_cons, dartImage, if_pos rfl]
    congr 1
    apply List.map_congr_left
    intro d hd
    rw [dartImage, if_neg]
    rintro rfl
    exact (List.nodup_cons.mp hnd).1 hd
  rw [hsuffix]
  change (((Delta.faceBoundary f).darts.rotate j.val).map (dartImage Delta f j hlen)).rotate
    ((Delta.faceBoundary f).darts.length - j.val) = _
  rw [List.map_rotate, List.rotate_rotate, Nat.add_sub_of_le (Nat.le_of_lt j.isLt)]
  simpa only [List.length_map] using
    List.rotate_length ((Delta.faceBoundary f).darts.map (dartImage Delta f j hlen))

/-- A relator cell, moved to the image of its face. -/
noncomputable def cell (hf : f ≠ Delta.outerFace)
    (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell (map Delta f j hlen) (keep Delta f j hlen Delta.outerFace) W where
  face := faceImage Delta f j hlen C.face
  face_ne_outer := fun h => C.face_ne_outer (faceImage_injective Delta f j hlen
    (h.trans (faceImage_of_ne Delta f j hlen hf.symm).symm))
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

theorem boundary_faceImage_word (g : Delta.toCombMap.Face) :
    (boundary Delta f j hlen (faceImage Delta f j hlen g)).darts.map (label Delta f j hlen) =
      (Delta.faceBoundary g).darts.map Delta.label := by
  by_cases hg : g = f
  · subst hg
    rw [faceImage_self]
    exact boundary_cellFace_word Delta g j hlen
  · rw [faceImage_of_ne Delta f j hlen hg]
    exact boundary_kept_word Delta f j hlen hg

/-- **The doubled diagram.** -/
noncomputable def diagram (hf : f ≠ Delta.outerFace) : DiscDiagram.{u, w, v} W where
  toCombMap := map Delta f j hlen
  planar := EdgeInsertion.planar Delta.toCombMap _ _ Delta.planar
    (corners_face_eq Delta.toCombMap (rebased Delta f j) (second Delta f j hlen))
  label := label Delta f j hlen
  label_alpha := insertLabel_alpha Delta.toCombMap Delta.label Delta.label_alpha _ _ _
  outerFace := keep Delta f j hlen Delta.outerFace
  faceBoundary := boundary Delta f j hlen
  relatorCells := Delta.relatorCells.map (cell Delta f j hlen hf)
  relatorCell_faces_nodup := by
    have heq : (Delta.relatorCells.map (cell Delta f j hlen hf)).map RelatorCell.face =
        (Delta.relatorCells.map RelatorCell.face).map (faceImage Delta f j hlen) := by
      rw [List.map_map, List.map_map]
      rfl
    rw [heq]
    exact Delta.relatorCell_faces_nodup.map (faceImage_injective Delta f j hlen)
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    exact (Delta.relatorCell_word C₀ hC₀).trans (boundary_faceImage_word Delta f j hlen C₀.face).symm
  inner_face := by
    intro F hF
    rcases face_partition Delta.toCombMap (rebased Delta f j) (second Delta f j hlen) F with
      hpre | hsuf | ⟨g, hg, hkept⟩
    · right
      rw [hpre]
      exact boundary_digon_value Delta f j hlen
    · rcases Delta.inner_face f hf with ⟨C, hC, hCf⟩ | hval
      · left
        refine ⟨cell Delta f j hlen hf C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change faceImage Delta f j hlen C.face = F
        rw [hCf, faceImage_self, hsuf]
      · right
        rw [hsuf, boundary_cellFace_word]
        exact hval
    · have hgo : g ≠ Delta.outerFace := by
        intro h
        exact hF (hkept.trans (congrArg (keep Delta f j hlen) h))
      rcases Delta.inner_face g hgo with ⟨C, hC, hCg⟩ | hval
      · left
        refine ⟨cell Delta f j hlen hf C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change faceImage Delta f j hlen C.face = F
        rw [hCg, faceImage_of_ne Delta f j hlen hg, hkept]
      · right
        rw [hkept, boundary_kept_word Delta f j hlen hg]
        exact hval
  boundary_product := by
    have hvalues : (Delta.relatorCells.map (cell Delta f j hlen hf)).map RelatorCell.value =
        Delta.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      rfl
    exact (congrArg List.prod hvalues).trans (Delta.boundary_product.trans
      (congrArg (fun word => RelLetter.listVal (RelWord.revInv word))
        (boundary_kept_word Delta f j hlen hf.symm).symm))

theorem boundaryWord_eq (hf : f ≠ Delta.outerFace) :
    (diagram Delta f j hlen hf).boundaryWord = Delta.boundaryWord :=
  congrArg RelWord.revInv (boundary_kept_word Delta f j hlen hf.symm)

/-- The relator cells, literally. -/
noncomputable def cellMap (hf : f ≠ Delta.outerFace) :
    OrderedRCellMap Delta (diagram Delta f j hlen hf) (faceImage Delta f j hlen) where
  cell := cell Delta f j hlen hf
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

noncomputable def replacement (hf : f ≠ Delta.outerFace) :
    OrderedGRegionReplacement.{u, w, v, v} Delta where
  diagram := diagram Delta f j hlen hf
  outerWord_eq := boundaryWord_eq Delta f j hlen hf
  cells := (cellMap Delta f j hlen hf).orderedTransport

noncomputable def oEquivalent (hf : f ≠ Delta.outerFace) :
    OEquivalentDiscDiagram Delta (diagram Delta f j hlen hf) :=
  (replacement Delta f j hlen hf).oEquivalent

theorem reduced (hf : f ≠ Delta.outerFace) (hred : Delta.Reduced) :
    (diagram Delta f j hlen hf).Reduced :=
  (replacement Delta f j hlen hf).reduced hred

theorem rCellCount_eq (hf : f ≠ Delta.outerFace) :
    (diagram Delta f j hlen hf).rCellCount = Delta.rCellCount :=
  (cellMap Delta f j hlen hf).orderedTransport.rCellCount_eq

theorem label_admissible (hf : f ≠ Delta.outerFace) (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (d : (diagram Delta f j hlen hf).toCombMap.Dart) :
    D.IsLetter ((diagram Delta f j hlen hf).label d) :=
  insertLabel_admissible Delta.toCombMap D hsymm Delta.label hlabel _ (hlabel _) d

end GroupApproximation.GGT.VanKampen.FaceEdgeDoubling

#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.dart_eq_get
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.boundary_cellFace_darts
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.label_admissible
