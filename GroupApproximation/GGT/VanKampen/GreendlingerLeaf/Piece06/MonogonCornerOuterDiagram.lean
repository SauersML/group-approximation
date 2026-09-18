import GroupApproximation.GGT.VanKampen.SurgeryMonogonDoubling
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: doubling the edge of a one-edge exterior

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `MonogonDoubling.diagram` doubles the
only dart of an inner monogon face.  This file doubles the only dart of the exterior when the
exterior is a monogon (`hlen`).  The inserted edge goes from the corner of the dart to itself.
Its face `cellFace` is the new exterior, a monogon reading the old outer word.  The new digon
has value one, so it is a G-face.  The relator cells move to the images of their faces
(`outerCell`), so the new diagram is O-equivalent to the old one (`outerOEquivalent`).  Every
old face other than the exterior keeps its traversal (`outerEmbedding`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

universe u w v

open HullSC

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

variable (X : DiscDiagram.{u, w, v} W)

/-- A relator cell, moved to the image of its face. -/
noncomputable def outerCell (C : RelatorCell X.toCombMap X.outerFace W) :
    RelatorCell (MonogonDoubling.map X X.outerFace) (MonogonDoubling.cellFace X X.outerFace) W where
  face := MonogonDoubling.faceImage X X.outerFace C.face
  face_ne_outer h := MonogonDoubling.keep_ne_cellFace X X.outerFace C.face_ne_outer
    ((MonogonDoubling.faceImage_of_ne X X.outerFace C.face_ne_outer).symm.trans h)
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

/-- **The doubled diagram of a one-edge exterior.** -/
noncomputable def outerDiagram (hlen : (X.faceBoundary X.outerFace).darts.length = 1) :
    DiscDiagram.{u, w, v} W where
  toCombMap := MonogonDoubling.map X X.outerFace
  planar := EdgeInsertion.planar X.toCombMap _ _ X.planar
    (EdgeInsertion.corners_face_eq X.toCombMap (X.faceBoundary X.outerFace)
      (MonogonDoubling.zero X X.outerFace))
  label := MonogonDoubling.label X X.outerFace
  label_alpha := EdgeInsertion.insertLabel_alpha X.toCombMap X.label X.label_alpha _ _ _
  outerFace := MonogonDoubling.cellFace X X.outerFace
  faceBoundary := MonogonDoubling.boundary X X.outerFace
  relatorCells := X.relatorCells.map (outerCell X)
  relatorCell_faces_nodup := by
    have heq : (X.relatorCells.map (outerCell X)).map RelatorCell.face =
        (X.relatorCells.map RelatorCell.face).map (MonogonDoubling.faceImage X X.outerFace) := by
      rw [List.map_map, List.map_map]
      rfl
    rw [heq]
    exact X.relatorCell_faces_nodup.map (MonogonDoubling.faceImage_injective X X.outerFace)
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    exact (X.relatorCell_word C₀ hC₀).trans
      (MonogonDoubling.boundary_faceImage_word X X.outerFace hlen C₀.face).symm
  inner_face := by
    intro F hF
    rcases EdgeInsertion.face_partition X.toCombMap (X.faceBoundary X.outerFace)
        (MonogonDoubling.zero X X.outerFace) F with hpre | hsuf | ⟨g, hg, hkept⟩
    · exact (hF hpre).elim
    · right
      rw [hsuf]
      exact MonogonDoubling.boundary_digon_value X X.outerFace hlen
    · rcases X.inner_face g hg with ⟨C, hC, hCg⟩ | hval
      · left
        refine ⟨outerCell X C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change MonogonDoubling.faceImage X X.outerFace C.face = F
        rw [hCg, MonogonDoubling.faceImage_of_ne X X.outerFace hg, hkept]
      · right
        rw [hkept, MonogonDoubling.boundary_kept_word X X.outerFace hg]
        exact hval
  boundary_product := by
    have hvalues : (X.relatorCells.map (outerCell X)).map RelatorCell.value =
        X.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      rfl
    exact (congrArg List.prod hvalues).trans (X.boundary_product.trans
      (congrArg (fun word => RelLetter.listVal (RelWord.revInv word))
        (MonogonDoubling.boundary_cellFace_word X X.outerFace hlen).symm))

variable (hlen : (X.faceBoundary X.outerFace).darts.length = 1)

theorem outerBoundaryWord_eq : (outerDiagram X hlen).boundaryWord = X.boundaryWord :=
  congrArg RelWord.revInv (MonogonDoubling.boundary_cellFace_word X X.outerFace hlen)

/-- The relator cells, literally. -/
noncomputable def outerCellMap :
    Surgery.OrderedRCellMap X (outerDiagram X hlen) (MonogonDoubling.faceImage X X.outerFace) where
  cell := outerCell X
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

noncomputable def outerReplacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} X where
  diagram := outerDiagram X hlen
  outerWord_eq := outerBoundaryWord_eq X hlen
  cells := (outerCellMap X hlen).orderedTransport

noncomputable def outerOEquivalent : OEquivalentDiscDiagram X (outerDiagram X hlen) :=
  (outerReplacement X hlen).oEquivalent

theorem outerLabel_letter (D : RelGenSet G Lambda)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (d : (outerDiagram X hlen).toCombMap.Dart) :
    (symmetricLabelAlphabet D).IsLetter ((outerDiagram X hlen).label d) :=
  EdgeInsertion.insertLabel_admissible X.toCombMap (symmetricLabelAlphabet D)
    (symmetricLabelAlphabet.symmetric D) X.label hlabel _
    (isLetter_relWordInv (symmetricLabelAlphabet D) (symmetricLabelAlphabet.symmetric D)
      (hlabel _)) d

/-- **The retained old darts and faces**; the old exterior goes to the new exterior. -/
noncomputable def outerEmbedding : DiscEmbeddingAway X (outerDiagram X hlen) X.outerFace where
  darts := ⟨EdgeInsertion.embed X.toCombMap, EdgeInsertion.embed_injective X.toCombMap⟩
  faces := ⟨MonogonDoubling.faceImage X X.outerFace,
    MonogonDoubling.faceImage_injective X X.outerFace⟩
  alpha _ := rfl
  label _ := rfl
  outer := (MonogonDoubling.faceImage_self X X.outerFace).symm
  face_boundary g hg :=
    (congrArg (fun F => (MonogonDoubling.boundary X X.outerFace F).darts)
      (MonogonDoubling.faceImage_of_ne X X.outerFace hg)).trans
      (MonogonDoubling.boundary_kept X X.outerFace hg)
  facePerm d hd := EdgeInsertion.facePerm_embed_of_ne X.toCombMap _ _ d
    (EdgeInsertion.corners_face_eq X.toCombMap (X.faceBoundary X.outerFace)
      (MonogonDoubling.zero X X.outerFace))
    (by rwa [EdgeInsertion.firstCorner_face X.toCombMap (X.faceBoundary X.outerFace)])

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.outerDiagram
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.outerOEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.outerEmbedding
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.outerCell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.outerBoundaryWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.outerCellMap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.outerReplacement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.outerLabel_letter
