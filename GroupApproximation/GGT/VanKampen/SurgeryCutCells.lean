import GroupApproximation.GGT.VanKampen.SurgeryFaceDiagram

/-!
# The relator cells kept by a region collapse

A cut keeps the relator cells whose face survives the collapse and rebases them
at the basepoint of the enclosing walk.  Rebasing multiplies every conjugator on
the left by one fixed element `c`, so every kept cell's value is the old value
conjugated by `c`, which is what the reducedness transport of `SurgeryCutReduced`
asks for.

The kept cells are indexed by the subtype of source cells whose face is kept, so
they arrive as the image of one index list under two maps: the inclusion into the
source cells and the rebasing into the cells of the replacement.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

/-- The value of a based relator cell, with the orientation choice isolated
inside the conjugation. -/
theorem RelatorCell.value_eq_conj {G : Type u} [Group G] {Lambda : Type w}
    {M : CombMap.{v}} {outer : M.Face}
    {W : Set (List (GGT.RelLetter G Lambda))} (C : RelatorCell M outer W) :
    C.value = C.conjugator *
      (if C.reversed then (GGT.RelLetter.listVal C.word)⁻¹
        else GGT.RelLetter.listVal C.word) * C.conjugator⁻¹ := by
  rw [RelatorCell.value]
  cases C.reversed
  · rfl
  · rfl

namespace Surgery
namespace MapCollapse

/-! ## The kept faces are distinct from each other and from the new face -/

theorem keptFace_ne_newFace (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (g : M.Face) (hg : g ∉ faces) :
    keptFace M faces region g hg ≠ newFace M faces region := by
  intro h
  have h1 : replaceGRegionFaceEquiv M faces region
      (keptFace M faces region g hg) = Sum.inl ⟨g, hg⟩ :=
    (replaceGRegionFaceEquiv M faces region).apply_symm_apply (Sum.inl ⟨g, hg⟩)
  have h2 : replaceGRegionFaceEquiv M faces region (newFace M faces region) =
      Sum.inr PUnit.unit :=
    (replaceGRegionFaceEquiv M faces region).apply_symm_apply
      (Sum.inr PUnit.unit)
  rw [h, h2] at h1
  simp at h1

theorem keptFace_inj (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (g g' : M.Face) (hg : g ∉ faces)
    (hg' : g' ∉ faces)
    (h : keptFace M faces region g hg = keptFace M faces region g' hg') :
    g = g' := by
  have h1 : replaceGRegionFaceEquiv M faces region
      (keptFace M faces region g hg) = Sum.inl ⟨g, hg⟩ :=
    (replaceGRegionFaceEquiv M faces region).apply_symm_apply (Sum.inl ⟨g, hg⟩)
  have h2 : replaceGRegionFaceEquiv M faces region
      (keptFace M faces region g' hg') = Sum.inl ⟨g', hg'⟩ :=
    (replaceGRegionFaceEquiv M faces region).apply_symm_apply
      (Sum.inl ⟨g', hg'⟩)
  rw [h, h2] at h1
  have hsub := Sum.inl_injective h1
  exact (congrArg (fun z : {f : M.Face // f ∉ faces} => z.1) hsub).symm

/-! ## The rebased cells -/

/-- A relator cell whose face survives the collapse, rebased at the basepoint of
the enclosing walk. -/
noncomputable def keptRelatorCell {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (outside : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap outside) (c : G)
    (C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ outside}) :
    RelatorCell (replaceGRegion Delta.toCombMap outside region)
      (newFace Delta.toCombMap outside region) W where
  face := keptFace Delta.toCombMap outside region C.1.face C.2
  face_ne_outer :=
    keptFace_ne_newFace Delta.toCombMap outside region C.1.face C.2
  word := C.1.word
  word_mem := C.1.word_mem
  conjugator := c⁻¹ * C.1.conjugator
  reversed := C.1.reversed

theorem keptRelatorCell_face {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (outside : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap outside) (c : G)
    (C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ outside}) :
    (keptRelatorCell Delta outside region c C).face =
      keptFace Delta.toCombMap outside region C.1.face C.2 := rfl

theorem keptRelatorCell_word {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (outside : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap outside) (c : G)
    (C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ outside}) :
    (keptRelatorCell Delta outside region c C).word = C.1.word := rfl

/-- Rebasing conjugates the value of a cell by the basepoint element. -/
theorem keptRelatorCell_value {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (outside : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap outside) (c : G)
    (C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ outside}) :
    (keptRelatorCell Delta outside region c C).value = c⁻¹ * C.1.value * c := by
  have hrev : (keptRelatorCell Delta outside region c C).reversed =
      C.1.reversed := rfl
  have hword : (keptRelatorCell Delta outside region c C).word = C.1.word := rfl
  have hconj : (keptRelatorCell Delta outside region c C).conjugator =
      c⁻¹ * C.1.conjugator := rfl
  rw [RelatorCell.value_eq_conj, RelatorCell.value_eq_conj, hrev, hword, hconj]
  group

/-- The faces of distinct kept cells are distinct exactly when the source faces
are, so a duplicate-free ordered cell list stays duplicate-free. -/
theorem keptRelatorCell_face_inj {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (outside : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap outside) (c : G)
    (C C' : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ outside})
    (h : (keptRelatorCell Delta outside region c C).face =
      (keptRelatorCell Delta outside region c C').face) :
    C.1.face = C'.1.face :=
  keptFace_inj Delta.toCombMap outside region C.1.face C'.1.face C.2 C'.2 h

end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
