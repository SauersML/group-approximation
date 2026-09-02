import GroupApproximation.GGT.VanKampen.CactusPowerBigBoundary
import GroupApproximation.GGT.VanKampen.RelativeDiscRealization

/-!
# Planar realization of a geodesic power diagram

This file combines the power-cactus rotation system, its labels, and the
explicit complementary face boundary.  Its disc boundary is literally the
repeated relative word, so component letters are not replaced by base letters.
The distinguished traversal and its partition into `n` consecutive copies are
exposed separately from the planar realization.

The resulting `DiscDiagram` has one relator face for every algebraic oriented
cell, in algebraic order.  Algebraic no-cancelling-pair reducedness transfers
directly to this ordered planar cell list.
-/

namespace GroupApproximation
namespace HullSC
namespace Lemma49GeodesicPowerDiagram

open GGT.VanKampen

universe u w

/-- Use the explicit complementary boundary on the big face and the canonical
polygon boundary on every other face. -/
noncomputable def cactusFaceBoundary
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n)
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
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n)
    {f : Z.cactusShape.toCombMap.Face} (h : f ≠ Z.cactusShape.bigFace) :
    Z.cactusFaceBoundary f = Z.cactusShape.faceBoundary f := by
  rw [cactusFaceBoundary, dif_neg h]

/-- On the big face, the custom selector is the explicit complementary
boundary. -/
theorem cactusFaceBoundary_big
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    Z.cactusFaceBoundary Z.cactusShape.bigFace =
      Z.cactusBigFaceBoundary := by
  rw [cactusFaceBoundary, dif_pos rfl]

/-- The custom outer boundary reads the prescribed closed-map outer word. -/
theorem cactus_customOuterFaceWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    (Z.cactusFaceBoundary Z.cactusShape.outerFace).darts.map Z.cactusLabel =
      Z.cactusOuterFaceWord := by
  rw [Z.cactusFaceBoundary_of_ne_big
    Z.cactusShape.bigFace_ne_outerFace.symm]
  exact Z.cactus_outerFaceWord

/-- The custom boundary of a relator face reads its geometric relator word. -/
theorem cactus_customRelatorFaceWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n)
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
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n)
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
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n)
    (C : RelatorCell Z.cactusShape.toCombMap Z.cactusShape.outerFace
      (RelWord.symmetrized v))
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
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    DiscDiagram.{u, w, 0} (RelWord.symmetrized v) where
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
    change g ^ n = GGT.RelLetter.listVal
      (RelWord.revInv
        ((Z.cactusFaceBoundary Z.cactusShape.outerFace).darts.map
          Z.cactusLabel))
    rw [Z.cactus_customOuterFaceWord, cactusOuterFaceWord,
      RelWord.revInv_revInv, listVal_lemma49BoundaryPower]
    have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
      simpa using Z.boundary_geodesic.2.1
    rw [hvalue]

/-- The disc boundary word is the literal repeated geodesic relative word. -/
theorem cactusDiscDiagram_boundaryWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    Z.cactusDiscDiagram.boundaryWord =
      lemma49BoundaryPower Z.boundaryWord n := by
  change RelWord.revInv
      ((Z.cactusFaceBoundary Z.cactusShape.outerFace).darts.map
        Z.cactusLabel) = _
  rw [Z.cactus_customOuterFaceWord, cactusOuterFaceWord,
    RelWord.revInv_revInv]

/-- The ordered planar relator-cell values are the original algebraic
factors. -/
theorem cactusDiscDiagram_cellValues
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    Z.cactusDiscDiagram.relatorCells.map RelatorCell.value = Z.factors :=
  Z.cactusRelatorCells_values

/-- Algebraic reducedness makes the explicit power cactus reduced. -/
theorem cactusDiscDiagram_reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    Z.cactusDiscDiagram.Reduced := by
  intro pre between suf C₁ C₂ hsplit
  apply Z.no_cancelling_pair
    (pre.map RelatorCell.value)
    (between.map RelatorCell.value)
    (suf.map RelatorCell.value) C₁.value C₂.value
  rw [← Z.cactusDiscDiagram_cellValues, hsplit]
  simp only [List.map_append, List.map_cons]

/-- Algebraic and planar relator cells have the same finite index type. -/
def cactusCellIndexEquiv
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    Fin Z.cells.length ≃ Fin Z.cactusDiscDiagram.rCellCount where
  toFun i := ⟨i, by
    change i.val < Z.cactusRelatorCells.length
    rw [cactusRelatorCells, List.length_ofFn]
    exact i.isLt⟩
  invFun j := ⟨j, by
    have hj : j.val < Z.cactusRelatorCells.length := j.isLt
    rw [cactusRelatorCells, List.length_ofFn] at hj
    exact hj⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv j := by apply Fin.ext; rfl

/-- The planar cell at the canonical index has the corresponding oriented
algebraic relator word. -/
theorem cactusCellIndexEquiv_word
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n)
    (i : Fin Z.cells.length) :
    (Z.cactusDiscDiagram.relatorCells.get
      (Z.cactusCellIndexEquiv i)).word = (Z.cells.get i).relator := by
  change ((List.ofFn fun j : Fin Z.cells.length ↦
    Z.cactusRelatorCell j).get (Z.cactusCellIndexEquiv i)).word = _
  rw [List.get_ofFn]
  change (Z.cellAt _).relator = (Z.cellAt i).relator
  apply congrArg HullSC.Lemma44OrientedRelatorCell.relator
  apply congrArg Z.cellAt
  apply Fin.ext
  rfl

end Lemma49GeodesicPowerDiagram
end HullSC

namespace GGT
namespace VanKampen

universe u w

open GroupApproximation.HullSC

/-- The recursive power word is the flattening of the list of its consecutive
copies. -/
theorem lemma49BoundaryPower_eq_flatten_replicate
    {Alpha : Type*} (word : List Alpha) : ∀ n : ℕ,
    lemma49BoundaryPower word n = (List.replicate n word).flatten
  | 0 => by simp [lemma49BoundaryPower]
  | n + 1 => by
      rw [lemma49BoundaryPower, lemma49BoundaryPower_eq_flatten_replicate]
      rw [List.replicate_succ, List.flatten_cons]

/-- The distinguished outer cycle of the power cactus.  The closed-map face
traversal starts at the canonical forward dart.  Reversing its orientation
gives the disc word, partitioned into exactly `n` copies of the geodesic
period. -/
structure Lemma49VKDesignatedBoundaryCycle
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) where
  baseDart : CactusDart Z.cactusShape
  baseDart_eq : baseDart = .outerForward Z.cactusShape.boundaryZero
  traversal : List (CactusDart Z.cactusShape)
  traversal_eq : traversal =
    (Z.cactusFaceBoundary Z.cactusShape.outerFace).darts
  traversal_nonempty : traversal ≠ []
  traversal_starts_at_base : traversal.head traversal_nonempty = baseDart
  traversal_from_base : traversal = List.ofFn
    (CactusDart.outerForward :
      Fin Z.cactusShape.boundaryLength → CactusDart Z.cactusShape)
  faceWord_eq : traversal.map Z.cactusLabel = Z.cactusOuterFaceWord
  boundaryCopies : List (List (GGT.RelLetter G Lambda))
  boundaryCopies_eq : boundaryCopies = List.replicate n Z.boundaryWord
  copies_count : boundaryCopies.length = n
  copies_are_periods : ∀ copy ∈ boundaryCopies, copy = Z.boundaryWord
  copies_flatten : boundaryCopies.flatten =
    lemma49BoundaryPower Z.boundaryWord n

/-- The explicit outer face and repeated-word partition give the designated
boundary cycle. -/
noncomputable def lemma49VKDesignatedBoundaryCycle
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    Lemma49VKDesignatedBoundaryCycle Z where
  baseDart := .outerForward Z.cactusShape.boundaryZero
  baseDart_eq := rfl
  traversal := List.ofFn (CactusDart.outerForward :
    Fin Z.cactusShape.boundaryLength → CactusDart Z.cactusShape)
  traversal_eq := by
    symm
    rw [Z.cactusFaceBoundary_of_ne_big
      Z.cactusShape.bigFace_ne_outerFace.symm,
      Z.cactusShape.faceBoundary_outerFace_darts,
      HullSC.Lemma49GeodesicPowerDiagram.cactus_outerBoundary_darts]
  traversal_nonempty :=
    (List.ofFn_eq_nil_iff.not.mpr (Nat.ne_of_gt Z.cactusShape.boundary_pos))
  traversal_starts_at_base := by
    rw [List.head_ofFn
      (List.ofFn_eq_nil_iff.not.mpr (Nat.ne_of_gt Z.cactusShape.boundary_pos))]
    congr 1
    apply Fin.ext
    rfl
  traversal_from_base := by
    rfl
  faceWord_eq := by
    have htr :
        List.ofFn (CactusDart.outerForward :
          Fin Z.cactusShape.boundaryLength → CactusDart Z.cactusShape) =
          (Z.cactusFaceBoundary Z.cactusShape.outerFace).darts := by
      rw [Z.cactusFaceBoundary_of_ne_big
        Z.cactusShape.bigFace_ne_outerFace.symm,
        Z.cactusShape.faceBoundary_outerFace_darts,
        HullSC.Lemma49GeodesicPowerDiagram.cactus_outerBoundary_darts]
    rw [htr]
    exact Z.cactus_customOuterFaceWord
  boundaryCopies := List.replicate n Z.boundaryWord
  boundaryCopies_eq := rfl
  copies_count := List.length_replicate
  copies_are_periods := by
    intro copy hcopy
    exact List.eq_of_mem_replicate hcopy
  copies_flatten :=
    (lemma49BoundaryPower_eq_flatten_replicate Z.boundaryWord n).symm

/-- A source-ready planar realization of the algebraic geodesic power
diagram, with cell indices, literal outer word, reducedness, and its
distinguished boundary cycle. -/
structure RelativeDiscRealizationPower
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (v : List (GGT.RelLetter G Lambda)) (g : G) (n : ℕ)
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) where
  diagram : DiscDiagram.{u, w, 0} (RelWord.symmetrized v)
  cellIndex : Fin Z.cells.length ≃ Fin diagram.rCellCount
  cellWord_eq : ∀ i : Fin Z.cells.length,
    (diagram.relatorCells.get (cellIndex i)).word = (Z.cells.get i).relator
  outerWord_eq : diagram.boundaryWord =
    lemma49BoundaryPower Z.boundaryWord n
  reduced : diagram.Reduced
  designatedBoundary : Lemma49VKDesignatedBoundaryCycle Z

namespace RelativeDiscRealizationPower

/-- The consecutive-copy partition flattens to the literal outer word of the
realized disc diagram. -/
theorem boundaryCopies_flatten_eq_outerWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    {Z : HullSC.Lemma49GeodesicPowerDiagram D v g n}
    (C : RelativeDiscRealizationPower D v g n Z) :
    C.designatedBoundary.boundaryCopies.flatten = C.diagram.boundaryWord :=
  C.designatedBoundary.copies_flatten.trans C.outerWord_eq.symm

end RelativeDiscRealizationPower

/-- The explicit power cactus supplies the source-ready realization. -/
noncomputable def relativeDiscRealizationPower
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    RelativeDiscRealizationPower D v g n Z where
  diagram := Z.cactusDiscDiagram
  cellIndex := Z.cactusCellIndexEquiv
  cellWord_eq := Z.cactusCellIndexEquiv_word
  outerWord_eq := Z.cactusDiscDiagram_boundaryWord
  reduced := Z.cactusDiscDiagram_reduced
  designatedBoundary := lemma49VKDesignatedBoundaryCycle Z

/-- Every geodesic power diagram has the explicit reduced planar
realization. -/
theorem relativeDiscRealizationPower_exists
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    Nonempty (RelativeDiscRealizationPower D v g n Z) :=
  ⟨relativeDiscRealizationPower D Z⟩

end VanKampen
end GGT
end GroupApproximation
