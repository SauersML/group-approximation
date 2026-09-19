import GroupApproximation.GGT.VanKampen.CactusBigBoundary

/-!
# Realization of an algebraic diagram by a planar cactus

This file combines the polygon rotation system, its labels, and the explicit
complementary face boundary.  The outer and relator faces keep the canonical
forward polygon traversals.  The complementary face uses the traversal proved
in `CactusBigBoundary`, whose word has value one, so it is a `G`-cell in the
relative presentation.

The resulting `DiscDiagram` has one relator face for every algebraic oriented
cell, in algebraic order.  Its outer word is the prescribed boundary word and
its relator-cell values are the prescribed factor list.  This proves
`CactusRealizationStatement`; the reducedness theorem in `DiscDiagram` then
transfers the algebraic no-cancelling-pair condition to the planar diagram.
-/

namespace GroupApproximation
namespace HullSC
namespace Lemma44OrientedRelatorDiagram

open GGT.VanKampen

universe u w

/-- Use the explicit complementary boundary on the big face and the canonical
polygon boundary on every other face. -/
noncomputable def cactusFaceBoundary
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (f : Z.cactusShape.toCombMap.Face) :
    FaceBoundary Z.cactusShape.toCombMap f := by
  classical
  exact if h : f = Z.cactusShape.bigFace then
      h.symm ▸ Z.cactusBigFaceBoundary
    else
      Z.cactusShape.faceBoundary f

/-- Away from the big face, the custom selector is the canonical polygon
boundary. -/
theorem cactusFaceBoundary_of_ne_big
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    {f : Z.cactusShape.toCombMap.Face} (h : f ≠ Z.cactusShape.bigFace) :
    Z.cactusFaceBoundary f = Z.cactusShape.faceBoundary f := by
  rw [cactusFaceBoundary, dif_neg h]

/-- On the big face, the custom selector is the explicit complementary
boundary. -/
theorem cactusFaceBoundary_big
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusFaceBoundary Z.cactusShape.bigFace =
      Z.cactusBigFaceBoundary := by
  rw [cactusFaceBoundary, dif_pos rfl]

/-- The custom outer boundary reads the prescribed closed-map outer word. -/
theorem cactus_customOuterFaceWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    (Z.cactusFaceBoundary Z.cactusShape.outerFace).darts.map Z.cactusLabel =
      Z.cactusOuterFaceWord := by
  rw [Z.cactusFaceBoundary_of_ne_big
    Z.cactusShape.bigFace_ne_outerFace.symm]
  exact Z.cactus_outerFaceWord

/-- The custom boundary of a relator face reads its geometric relator word. -/
theorem cactus_customRelatorFaceWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    (Z.cactusFaceBoundary (Z.cactusShape.relatorFace i)).darts.map
        Z.cactusLabel = (Z.geometricCell i).relator := by
  rw [Z.cactusFaceBoundary_of_ne_big
    (Z.cactusShape.bigFace_ne_relatorFace i).symm]
  exact Z.cactus_relatorFaceWord i

/-- A face whose classifier is `i` is the explicitly indexed face `i`. -/
theorem face_eq_indexedFace_of_faceEquiv_eq (S : CactusShape)
    (f : S.toCombMap.Face) (i : S.FaceIndex) (h : S.faceEquiv f = i) :
    f = S.indexedFace i := by
  rw [← S.indexedFace_faceEquiv f, h]

/-- Every nonouter cactus face is either its relator polygon or the value-one
complementary `G`-face. -/
theorem cactus_inner_face
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (f : Z.cactusShape.toCombMap.Face)
    (hf : f ≠ Z.cactusShape.outerFace) :
    (∃ C ∈ Z.cactusRelatorCells, C.face = f) ∨
      GGT.RelLetter.listVal
        ((Z.cactusFaceBoundary f).darts.map Z.cactusLabel) = 1 := by
  cases hi : Z.cactusShape.faceEquiv f with
  | outer =>
      have hface : f = Z.cactusShape.outerFace :=
        face_eq_indexedFace_of_faceEquiv_eq Z.cactusShape f .outer hi
      exact (hf hface).elim
  | relator i =>
      left
      let j : Fin Z.cells.length := i.rev
      refine ⟨Z.cactusRelatorCell j, ?_, ?_⟩
      · rw [cactusRelatorCells, List.mem_ofFn]
        exact ⟨j, rfl⟩
      · change Z.cactusShape.relatorFace j.rev = f
        simp only [j, Fin.rev_rev]
        exact (face_eq_indexedFace_of_faceEquiv_eq Z.cactusShape
          f (.relator i) hi).symm
  | big =>
      right
      have hface : f = Z.cactusShape.bigFace :=
        face_eq_indexedFace_of_faceEquiv_eq Z.cactusShape f .big hi
      subst f
      rw [Z.cactusFaceBoundary_big, Z.cactusBigFaceBoundary_darts]
      exact Z.cactusBigDarts_value

/-- Every stored cactus relator word is the word read on its custom face
boundary. -/
theorem cactusRelatorCells_customWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (C : RelatorCell Z.cactusShape.toCombMap Z.cactusShape.outerFace W)
    (hC : C ∈ Z.cactusRelatorCells) :
    C.word = (Z.cactusFaceBoundary C.face).darts.map Z.cactusLabel := by
  rw [cactusRelatorCells, List.mem_ofFn] at hC
  obtain ⟨i, rfl⟩ := hC
  change (Z.cellAt i).relator =
    (Z.cactusFaceBoundary (Z.cactusShape.relatorFace i.rev)).darts.map
      Z.cactusLabel
  rw [Z.cactus_customRelatorFaceWord, Z.geometricCell_rev]

/-- The explicit polygon cactus as a planar relative disc diagram. -/
noncomputable def cactusDiscDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    DiscDiagram.{u, w, 0} W where
  toCombMap := Z.cactusShape.toCombMap
  planar := Z.cactusShape.planar
  label := Z.cactusLabel
  label_alpha := Z.cactusLabel_alpha
  outerFace := Z.cactusShape.outerFace
  faceBoundary := Z.cactusFaceBoundary
  relatorCells := Z.cactusRelatorCells
  relatorCell_faces_nodup := Z.cactusRelatorCells_faces_nodup
  relatorCell_word := Z.cactusRelatorCells_customWord
  inner_face := Z.cactus_inner_face
  boundary_product := by
    rw [Z.cactusRelatorCells_values, Z.factors_prod]
    change Z.boundary = GGT.RelLetter.listVal
      (RelWord.revInv
        ((Z.cactusFaceBoundary Z.cactusShape.outerFace).darts.map
          Z.cactusLabel))
    rw [Z.cactus_customOuterFaceWord, cactusOuterFaceWord,
      RelWord.revInv_revInv, HullSC.listVal_map_base,
      Z.boundaryWord_isWord.prod_eq]

/-- The disc boundary word of the explicit cactus is the prescribed base
word. -/
theorem cactusDiscDiagram_boundaryWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusDiscDiagram.boundaryWord =
      Z.boundaryWord.map
        (GGT.RelLetter.base : G → GGT.RelLetter G Lambda) := by
  change RelWord.revInv
      ((Z.cactusFaceBoundary Z.cactusShape.outerFace).darts.map
        Z.cactusLabel) = _
  rw [Z.cactus_customOuterFaceWord, cactusOuterFaceWord,
    RelWord.revInv_revInv]

/-- The explicit disc diagram supplies the promised cactus realization. -/
noncomputable def cactusRealization
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    CactusRealization Z where
  diagram := Z.cactusDiscDiagram
  boundaryWord_eq := Z.cactusDiscDiagram_boundaryWord
  cellValues_eq := Z.cactusRelatorCells_values

end Lemma44OrientedRelatorDiagram
end HullSC

namespace GGT
namespace VanKampen

universe u w

/-- Every oriented least-area algebraic diagram has the explicit planar
cactus realization. -/
theorem cactusRealizationStatement : CactusRealizationStatement.{u, w} := by
  intro G _ Lambda A W R Z
  exact ⟨HullSC.Lemma44OrientedRelatorDiagram.cactusRealization Z⟩

end VanKampen
end GGT
end GroupApproximation
