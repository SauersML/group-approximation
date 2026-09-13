import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoubling
import GroupApproximation.GGT.VanKampen.DiscEmbeddingAway
import GroupApproximation.Meta.AxiomGuard

/-!
# Doubling the edge of a monogon

`FaceEdgeDoubling` doubles a dart `w_j` of an inner face `f` by an edge from the corner before
`w_j` to the corner after it, and needs `f` to have at least two darts.  When `f` is a monogon
`[d]` the two corners are one corner.  Inserting an edge from that corner to itself
(`EdgeInsertion.splitMap` at index zero) gives a monogon `[none]` and a digon `[some none, d]`
(`boundary_cellFace`, `boundary_digon`).  The new dart `none` carries the label of `d`, so the
monogon reads the old word of `f` with `none` in the place of `d`, and the digon, a G-face,
has value one.  Every other face keeps its darts.

The result is O-equivalent, keeps reducedness and label legality, and is planar
(`EdgeInsertion.planar`).  Every old dart survives, so the landed transport of
`DiscEmbeddingAway` applies to any region avoiding `f` (`embedding`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.MonogonDoubling

open HullSC HullSC.Lemma44OrientedRelatorDiagram EdgeInsertion Surgery
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)

/-- The index of the only corner. -/
def zero : Fin (Delta.faceBoundary f).darts.length :=
  ⟨0, List.length_pos_iff.mpr (Delta.faceBoundary f).nonempty⟩

/-- The doubled dart. -/
def dart : Delta.toCombMap.Dart := firstCorner Delta.toCombMap (Delta.faceBoundary f)

theorem dart_face : Delta.toCombMap.faceOf (dart Delta f) = f :=
  firstCorner_face Delta.toCombMap (Delta.faceBoundary f)

theorem darts_eq (hmono : (Delta.faceBoundary f).darts.length = 1) :
    (Delta.faceBoundary f).darts = [dart Delta f] := by
  have h := FaceEdgeDoubling.darts_eq_cons (Delta.faceBoundary f)
  have hdrop : (Delta.faceBoundary f).darts.drop 1 = [] := List.drop_eq_nil_iff.mpr (by omega)
  rw [hdrop] at h
  exact h

theorem dart_eq_of_face (hmono : (Delta.faceBoundary f).darts.length = 1)
    {d : Delta.toCombMap.Dart} (hd : Delta.toCombMap.faceOf d = f) : dart Delta f = d := by
  have hmem : d ∈ (Delta.faceBoundary f).darts := ((Delta.faceBoundary f).mem_iff d).mpr hd
  rw [darts_eq Delta f hmono] at hmem
  exact (List.mem_singleton.mp hmem).symm

/-- The map with an edge from the corner of the monogon to itself. -/
noncomputable abbrev map : CombMap.{v} :=
  splitMap Delta.toCombMap (Delta.faceBoundary f) (zero Delta f)

/-- A retained face other than `f`. -/
noncomputable abbrev keep (g : Delta.toCombMap.Face) : (map Delta f).Face :=
  keptFace Delta.toCombMap (firstCorner Delta.toCombMap (Delta.faceBoundary f))
    (secondCorner Delta.toCombMap (Delta.faceBoundary f) (zero Delta f)) g

/-- The face `f`, with the new dart in the place of `d`. -/
noncomputable abbrev cellFace : (map Delta f).Face :=
  prefixFace Delta.toCombMap (Delta.faceBoundary f) (zero Delta f)

/-- The new digon. -/
noncomputable abbrev digon : (map Delta f).Face :=
  suffixFace Delta.toCombMap (Delta.faceBoundary f) (zero Delta f)

/-- Where an old face goes. -/
noncomputable def faceImage (g : Delta.toCombMap.Face) : (map Delta f).Face :=
  if g = f then cellFace Delta f else keep Delta f g

theorem faceImage_self : faceImage Delta f f = cellFace Delta f := if_pos rfl

theorem faceImage_of_ne {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    faceImage Delta f g = keep Delta f g := if_neg hg

theorem keep_ne_cellFace {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    keep Delta f g ≠ cellFace Delta f :=
  keptFace_ne_prefixFace Delta.toCombMap (Delta.faceBoundary f) (zero Delta f) g hg

theorem keep_ne_digon {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    keep Delta f g ≠ digon Delta f :=
  keptFace_ne_suffixFace Delta.toCombMap (Delta.faceBoundary f) (zero Delta f) g hg

theorem digon_ne_cellFace : digon Delta f ≠ cellFace Delta f :=
  (prefixFace_ne_suffixFace Delta.toCombMap (Delta.faceBoundary f) (zero Delta f)).symm

theorem keep_injective : Function.Injective (keep Delta f) :=
  keptFace_injective Delta.toCombMap _ _
    (corners_face_eq Delta.toCombMap (Delta.faceBoundary f) (zero Delta f))

theorem faceImage_injective : Function.Injective (faceImage Delta f) := by
  intro g h heq
  by_cases hg : g = f
  · by_cases hh : h = f
    · exact hg.trans hh.symm
    · rw [hg, faceImage_self, faceImage_of_ne Delta f hh] at heq
      exact (keep_ne_cellFace Delta f hh heq.symm).elim
  · by_cases hh : h = f
    · rw [hh, faceImage_self, faceImage_of_ne Delta f hg] at heq
      exact (keep_ne_cellFace Delta f hg heq).elim
    · rw [faceImage_of_ne Delta f hg, faceImage_of_ne Delta f hh] at heq
      exact keep_injective Delta f heq

theorem faceImage_ne_digon (g : Delta.toCombMap.Face) :
    faceImage Delta f g ≠ digon Delta f := by
  by_cases hg : g = f
  · rw [hg, faceImage_self]
    exact (digon_ne_cellFace Delta f).symm
  · rw [faceImage_of_ne Delta f hg]
    exact keep_ne_digon Delta f hg

/-- The labels: the new dart `none` carries the label of `d`, and its reverse the inverse. -/
noncomputable abbrev label : (map Delta f).Dart → RelLetter G Lambda :=
  insertLabel Delta.toCombMap Delta.label (RelWord.inv (Delta.label (dart Delta f)))

theorem label_none : label Delta f none = Delta.label (dart Delta f) :=
  RelWord.inv_inv_letter _

/-- Every face traversal. -/
noncomputable def boundary (F : (map Delta f).Face) : FaceBoundary (map Delta f) F :=
  allFaceBoundary Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary (zero Delta f) F

theorem boundary_darts (F : (map Delta f).Face) :
    (boundary Delta f F).darts =
      (allFaceBoundary Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary
        (zero Delta f) F).darts := rfl

theorem boundary_kept {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    (boundary Delta f (keep Delta f g)).darts =
      (Delta.faceBoundary g).darts.map (embed Delta.toCombMap) := by
  rw [boundary_darts]
  exact allFaceBoundary_kept Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary
    (zero Delta f) g hg

/-- **The monogon of the new dart.** -/
theorem boundary_cellFace : (boundary Delta f (cellFace Delta f)).darts = [none] := by
  rw [boundary_darts, allFaceBoundary_prefix]
  rfl

/-- **The digon**: the reverse of the new dart, then the old traversal of `f`. -/
theorem boundary_digon :
    (boundary Delta f (digon Delta f)).darts =
      some none :: (Delta.faceBoundary f).darts.map (embed Delta.toCombMap) := by
  rw [boundary_darts, allFaceBoundary_suffix]
  rfl

theorem boundary_kept_word {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    (boundary Delta f (keep Delta f g)).darts.map (label Delta f) =
      (Delta.faceBoundary g).darts.map Delta.label := by
  rw [boundary_darts]
  exact split_kept_word Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary
    (zero Delta f) g hg Delta.label (RelWord.inv (Delta.label (dart Delta f)))

/-- The face of `f` reads the old word of `f`. -/
theorem boundary_cellFace_word (hmono : (Delta.faceBoundary f).darts.length = 1) :
    (boundary Delta f (cellFace Delta f)).darts.map (label Delta f) =
      (Delta.faceBoundary f).darts.map Delta.label := by
  rw [boundary_cellFace, darts_eq Delta f hmono]
  change [label Delta f none] = [Delta.label (dart Delta f)]
  rw [label_none]

theorem boundary_digon_value (hmono : (Delta.faceBoundary f).darts.length = 1) :
    RelLetter.listVal ((boundary Delta f (digon Delta f)).darts.map (label Delta f)) = 1 := by
  rw [boundary_digon, darts_eq Delta f hmono]
  change RelLetter.listVal
    (RelWord.inv (Delta.label (dart Delta f)) :: [Delta.label (dart Delta f)]) = 1
  rw [RelWord.listVal_cons, RelWord.val_inv]
  change (Delta.label (dart Delta f)).val⁻¹ *
    ([Delta.label (dart Delta f)].map RelLetter.val).prod = 1
  rw [List.map_singleton, List.prod_singleton, inv_mul_cancel]

/-- The dart map onto the face of `f`: `d` goes to the new dart. -/
noncomputable def dartImage (d : Delta.toCombMap.Dart) : (map Delta f).Dart :=
  if d = dart Delta f then none else embed Delta.toCombMap d

theorem dartImage_dart : dartImage Delta f (dart Delta f) = none := if_pos rfl

/-- **The face of `f` is the old traversal with the new dart in the place of `d`.** -/
theorem boundary_cellFace_darts (hmono : (Delta.faceBoundary f).darts.length = 1) :
    (boundary Delta f (cellFace Delta f)).darts =
      (Delta.faceBoundary f).darts.map (dartImage Delta f) := by
  rw [boundary_cellFace, darts_eq Delta f hmono]
  exact congrArg (fun x => [x]) (dartImage_dart Delta f).symm

/-- A relator cell, moved to the image of its face. -/
noncomputable def cell (hf : f ≠ Delta.outerFace)
    (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell (map Delta f) (keep Delta f Delta.outerFace) W where
  face := faceImage Delta f C.face
  face_ne_outer := fun h => C.face_ne_outer (faceImage_injective Delta f
    (h.trans (faceImage_of_ne Delta f hf.symm).symm))
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

theorem boundary_faceImage_word (hmono : (Delta.faceBoundary f).darts.length = 1)
    (g : Delta.toCombMap.Face) :
    (boundary Delta f (faceImage Delta f g)).darts.map (label Delta f) =
      (Delta.faceBoundary g).darts.map Delta.label := by
  by_cases hg : g = f
  · subst hg
    rw [faceImage_self]
    exact boundary_cellFace_word Delta g hmono
  · rw [faceImage_of_ne Delta f hg]
    exact boundary_kept_word Delta f hg

variable (hf : f ≠ Delta.outerFace) (hmono : (Delta.faceBoundary f).darts.length = 1)

/-- **The doubled diagram.** -/
noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := map Delta f
  planar := EdgeInsertion.planar Delta.toCombMap _ _ Delta.planar
    (corners_face_eq Delta.toCombMap (Delta.faceBoundary f) (zero Delta f))
  label := label Delta f
  label_alpha := insertLabel_alpha Delta.toCombMap Delta.label Delta.label_alpha _ _ _
  outerFace := keep Delta f Delta.outerFace
  faceBoundary := boundary Delta f
  relatorCells := Delta.relatorCells.map (cell Delta f hf)
  relatorCell_faces_nodup := by
    have heq : (Delta.relatorCells.map (cell Delta f hf)).map RelatorCell.face =
        (Delta.relatorCells.map RelatorCell.face).map (faceImage Delta f) := by
      rw [List.map_map, List.map_map]
      rfl
    rw [heq]
    exact Delta.relatorCell_faces_nodup.map (faceImage_injective Delta f)
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    exact (Delta.relatorCell_word C₀ hC₀).trans
      (boundary_faceImage_word Delta f hmono C₀.face).symm
  inner_face := by
    intro F hF
    rcases face_partition Delta.toCombMap (Delta.faceBoundary f) (zero Delta f) F with
      hpre | hsuf | ⟨g, hg, hkept⟩
    · rcases Delta.inner_face f hf with ⟨C, hC, hCf⟩ | hval
      · left
        refine ⟨cell Delta f hf C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change faceImage Delta f C.face = F
        rw [hCf, faceImage_self, hpre]
      · right
        rw [hpre, boundary_cellFace_word Delta f hmono]
        exact hval
    · right
      rw [hsuf]
      exact boundary_digon_value Delta f hmono
    · have hgo : g ≠ Delta.outerFace := by
        intro h
        exact hF (hkept.trans (congrArg (keep Delta f) h))
      rcases Delta.inner_face g hgo with ⟨C, hC, hCg⟩ | hval
      · left
        refine ⟨cell Delta f hf C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change faceImage Delta f C.face = F
        rw [hCg, faceImage_of_ne Delta f hg, hkept]
      · right
        rw [hkept, boundary_kept_word Delta f hg]
        exact hval
  boundary_product := by
    have hvalues : (Delta.relatorCells.map (cell Delta f hf)).map RelatorCell.value =
        Delta.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      rfl
    exact (congrArg List.prod hvalues).trans (Delta.boundary_product.trans
      (congrArg (fun word => RelLetter.listVal (RelWord.revInv word))
        (boundary_kept_word Delta f hf.symm).symm))

theorem boundaryWord_eq : (diagram Delta f hf hmono).boundaryWord = Delta.boundaryWord :=
  congrArg RelWord.revInv (boundary_kept_word Delta f hf.symm)

/-- The relator cells, literally. -/
noncomputable def cellMap : OrderedRCellMap Delta (diagram Delta f hf hmono) (faceImage Delta f) where
  cell := cell Delta f hf
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

noncomputable def replacement : OrderedGRegionReplacement.{u, w, v, v} Delta where
  diagram := diagram Delta f hf hmono
  outerWord_eq := boundaryWord_eq Delta f hf hmono
  cells := (cellMap Delta f hf hmono).orderedTransport

noncomputable def oEquivalent : OEquivalentDiscDiagram Delta (diagram Delta f hf hmono) :=
  (replacement Delta f hf hmono).oEquivalent

theorem reduced (hred : Delta.Reduced) : (diagram Delta f hf hmono).Reduced :=
  (replacement Delta f hf hmono).reduced hred

theorem rCellCount_eq : (diagram Delta f hf hmono).rCellCount = Delta.rCellCount :=
  (cellMap Delta f hf hmono).orderedTransport.rCellCount_eq

theorem label_admissible (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hlabel : ∀ d, D.IsLetter (Delta.label d)) (d : (diagram Delta f hf hmono).toCombMap.Dart) :
    D.IsLetter ((diagram Delta f hf hmono).label d) :=
  insertLabel_admissible Delta.toCombMap D hsymm Delta.label hlabel _
    (isLetter_relWordInv D hsymm (hlabel _)) d

/-- The retained old darts and faces. -/
noncomputable def embedding : DiscEmbeddingAway Delta (diagram Delta f hf hmono) f where
  darts := ⟨embed Delta.toCombMap, embed_injective Delta.toCombMap⟩
  faces := ⟨keep Delta f, keep_injective Delta f⟩
  alpha _ := rfl
  label _ := rfl
  outer := rfl
  face_boundary _ hg := boundary_kept Delta f hg
  facePerm d hd := facePerm_embed_of_ne Delta.toCombMap _ _ d
    (corners_face_eq Delta.toCombMap (Delta.faceBoundary f) (zero Delta f))
    (by rwa [firstCorner_face Delta.toCombMap (Delta.faceBoundary f)])

end GroupApproximation.GGT.VanKampen.MonogonDoubling

#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.boundary_cellFace_darts
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.boundary_digon_value
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.label_admissible
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.embedding
