import GroupApproximation.GGT.VanKampen.PlanarVanKampenCells
import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.GGT.HullSCRelatorFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# Disc diagrams from planar maps

The cellular planar van Kampen lemma (`exists_cellFactors_of_planar`) makes a disc
diagram out of a labelled planar map with an outer face, a set of relator faces reading
relator words, and freely trivial remaining faces.  The relator cells of that diagram
are exactly the relator faces: `DiscDiagram.ofPlanar`, with
`DiscDiagram.ofPlanar_rCellCount` and `DiscDiagram.ofPlanar_boundaryWord`.

* `CellFactor.exists_faceBoundary`: a cell factor is a signed conjugate of the word read
  along any chosen boundary of its face.
* `exists_relatorCells_of_cellFactors`: based relator cells realizing a list of cell
  factors.
* `exists_relatorCells_of_planar`: the relator cells of a planar map, with product the
  value of the disc boundary.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}

/-- A cell factor is a signed conjugate of the word read along any chosen boundary of
its face. -/
theorem CellFactor.exists_faceBoundary {M : CombMap.{v}}
    {label : M.Dart → RelLetter G Lambda} {f : M.Face} {x : G}
    (h : CellFactor M label f x) (B : FaceBoundary M f) :
    ∃ (c : G) (b : Bool), x = if b then c * (RelLetter.listVal (B.darts.map label))⁻¹ * c⁻¹
      else c * RelLetter.listVal (B.darts.map label) * c⁻¹ := by
  obtain ⟨l, hl, c, hf, hx⟩ := h
  obtain ⟨k, hk, hrot⟩ :=
    B.isFaceCycle.exists_rotate_eq hl ((FaceBoundary.faceOf_head B).trans hf.symm)
  have hval : RelLetter.listVal (l.map label) =
      (RelLetter.listVal ((B.darts.map label).take k))⁻¹ *
        RelLetter.listVal (B.darts.map label) *
          RelLetter.listVal ((B.darts.map label).take k) := by
    rw [← hrot, List.map_rotate]
    exact RelWord.listVal_rotate _ (by rw [List.length_map]; exact hk)
  rcases hx with hx | hx
  · refine ⟨c * (RelLetter.listVal ((B.darts.map label).take k))⁻¹, false, ?_⟩
    rw [if_neg Bool.false_ne_true, hx, hval]
    group
  · refine ⟨c * (RelLetter.listVal ((B.darts.map label).take k))⁻¹, true, ?_⟩
    rw [if_pos (rfl : true = true), hx, hval]
    group

/-- Inverting every factor and reversing the list inverts the product. -/
theorem prod_map_snd_reverse_map_inv {α : Type*} (factors : List (α × G)) :
    (((factors.map fun y => (y.1, y.2⁻¹)).reverse).map Prod.snd).prod =
      ((factors.map Prod.snd).prod)⁻¹ := by
  simp only [List.map_reverse, List.map_map, List.prod_inv_reverse, Function.comp_def]

/-- **Based relator cells realizing cell factors.**  Every list of cell factors on
relator faces is the value list of a list of based relator cells on the same faces,
reading the chosen face boundaries. -/
theorem exists_relatorCells_of_cellFactors {M : CombMap.{v}}
    {label : M.Dart → RelLetter G Lambda} {outerFace : M.Face}
    {W : Set (List (RelLetter G Lambda))}
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face)
    (houter : outerFace ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W) :
    ∀ factors : List (M.Face × G), (∀ y ∈ factors, y.1 ∈ relFaces) →
      (∀ y ∈ factors, CellFactor M label y.1 y.2) →
      ∃ cells : List (RelatorCell M outerFace W),
        cells.map RelatorCell.face = factors.map Prod.fst ∧
        (∀ C ∈ cells, C.word = (faceBoundary C.face).darts.map label) ∧
        (cells.map RelatorCell.value).prod = (factors.map Prod.snd).prod
  | [], _, _ => ⟨[], rfl, fun _ hC => absurd hC List.not_mem_nil, rfl⟩
  | y :: ys, hmem, hfac => by
      obtain ⟨cells, hface, hword', hprod⟩ :=
        exists_relatorCells_of_cellFactors faceBoundary relFaces houter hword ys
          (fun z hz => hmem z (List.mem_cons_of_mem y hz))
          (fun z hz => hfac z (List.mem_cons_of_mem y hz))
      have hy : y.1 ∈ relFaces := hmem y List.mem_cons_self
      obtain ⟨c, b, hx⟩ :=
        (hfac y List.mem_cons_self).exists_faceBoundary (faceBoundary y.1)
      obtain ⟨C, hCface, hCword, hCval⟩ : ∃ C : RelatorCell M outerFace W, C.face = y.1 ∧
          C.word = (faceBoundary C.face).darts.map label ∧ C.value = y.2 :=
        ⟨{ face := y.1
           face_ne_outer := fun h => houter (by rw [← h]; exact hy)
           word := (faceBoundary y.1).darts.map label
           word_mem := hword y.1 hy
           conjugator := c
           reversed := b }, rfl, rfl, hx.symm⟩
      refine ⟨C :: cells, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.map_cons, hCface, hface]
      · intro C' hC'
        rcases List.mem_cons.mp hC' with rfl | hC'
        · exact hCword
        · exact hword' C' hC'
      · rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, hprod, hCval]

/-- **The relator cells of a planar map.**  In a labelled planar map with an outer face
and relator faces reading words of `W`, where every other face reads a freely trivial
word, there are based relator cells, one on each relator face, whose product is the
value of the disc boundary. -/
theorem exists_relatorCells_of_planar {W : Set (List (RelLetter G Lambda))}
    (M : CombMap.{v}) (hplanar : M.IsPlanar) (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d)) (outerFace : M.Face)
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face)
    (houter : outerFace ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W)
    (htriv : ∀ f, f ≠ outerFace → f ∉ relFaces →
      RelLetter.listVal ((faceBoundary f).darts.map label) = 1) :
    ∃ cells : List (RelatorCell M outerFace W), (cells.map RelatorCell.face).Nodup ∧
      (∀ f, f ∈ cells.map RelatorCell.face ↔ f ∈ relFaces) ∧
      (∀ C ∈ cells, C.word = (faceBoundary C.face).darts.map label) ∧
      (cells.map RelatorCell.value).prod =
        RelLetter.listVal (RelWord.revInv ((faceBoundary outerFace).darts.map label)) := by
  have htriv' : ∀ (l : List M.Dart) (hl : M.IsFaceCycle l),
      M.faceOf (l.head hl.ne_nil) ≠ M.faceOf ((faceBoundary outerFace).darts.head
        (faceBoundary outerFace).isFaceCycle.ne_nil) →
      M.faceOf (l.head hl.ne_nil) ∉ relFaces → RelLetter.listVal (l.map label) = 1 := by
    intro l hl hne hf
    obtain ⟨k, hk, hrot⟩ :=
      (faceBoundary (M.faceOf (l.head hl.ne_nil))).isFaceCycle.exists_rotate_eq hl
        (FaceBoundary.faceOf_head _)
    rw [← hrot, List.map_rotate]
    have hne' : M.faceOf (l.head hl.ne_nil) ≠ outerFace := by
      rwa [FaceBoundary.faceOf_head] at hne
    exact listVal_rotate_eq_one _ (by rw [List.length_map]; exact hk) (htriv _ hne' hf)
  obtain ⟨factors, hnd, hiff, hfac, hprod⟩ := exists_cellFactors_of_planar M.dartCount M rfl
    hplanar label label_alpha relFaces (faceBoundary outerFace).darts
    (faceBoundary outerFace).isFaceCycle
    (by rw [FaceBoundary.faceOf_head]; exact houter) htriv'
  have hmapfst : ((factors.map fun y => (y.1, y.2⁻¹)).reverse).map Prod.fst =
      (factors.map Prod.fst).reverse := by
    rw [List.map_reverse, List.map_map]
    rfl
  have hmem' : ∀ y ∈ (factors.map fun y => (y.1, y.2⁻¹)).reverse,
      y.1 ∈ relFaces ∧ CellFactor M label y.1 y.2 := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hy)
    exact ⟨(hiff z.1).mp (List.mem_map.mpr ⟨z, hz, rfl⟩), (hfac z hz).inv⟩
  obtain ⟨cells, hface, hword', hprodC⟩ := exists_relatorCells_of_cellFactors (W := W)
    faceBoundary relFaces houter hword ((factors.map fun y => (y.1, y.2⁻¹)).reverse)
    (fun y hy => (hmem' y hy).1) (fun y hy => (hmem' y hy).2)
  refine ⟨cells, ?_, fun f => ?_, hword', ?_⟩
  · rw [hface, hmapfst]
    exact List.nodup_reverse.mpr hnd
  · rw [hface, hmapfst, List.mem_reverse]
    exact hiff f
  · rw [hprodC, prod_map_snd_reverse_map_inv, hprod, RelWord.listVal_revInv]

/-- **The disc diagram of a planar map.**  A labelled planar map with an outer face,
relator faces reading words of `W`, and freely trivial remaining faces, as a disc
diagram whose relator cells lie exactly on the relator faces. -/
noncomputable def DiscDiagram.ofPlanar {W : Set (List (RelLetter G Lambda))}
    (M : CombMap.{v}) (hplanar : M.IsPlanar) (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d)) (outerFace : M.Face)
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face)
    (houter : outerFace ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W)
    (htriv : ∀ f, f ≠ outerFace → f ∉ relFaces →
      RelLetter.listVal ((faceBoundary f).darts.map label) = 1) :
    DiscDiagram.{u, w, v} W where
  toCombMap := M
  planar := hplanar
  label := label
  label_alpha := label_alpha
  outerFace := outerFace
  faceBoundary := faceBoundary
  relatorCells := (exists_relatorCells_of_planar (W := W) M hplanar label label_alpha
    outerFace faceBoundary relFaces houter hword htriv).choose
  relatorCell_faces_nodup := (exists_relatorCells_of_planar (W := W) M hplanar label
    label_alpha outerFace faceBoundary relFaces houter hword htriv).choose_spec.1
  relatorCell_word := (exists_relatorCells_of_planar (W := W) M hplanar label label_alpha
    outerFace faceBoundary relFaces houter hword htriv).choose_spec.2.2.1
  inner_face f hf := by
    by_cases h : f ∈ relFaces
    · obtain ⟨C, hC, hCf⟩ := List.mem_map.mp (((exists_relatorCells_of_planar (W := W) M
        hplanar label label_alpha outerFace faceBoundary relFaces houter hword
          htriv).choose_spec.2.1 f).mpr h)
      exact Or.inl ⟨C, hC, hCf⟩
    · exact Or.inr (htriv f hf h)
  boundary_product := (exists_relatorCells_of_planar (W := W) M hplanar label label_alpha
    outerFace faceBoundary relFaces houter hword htriv).choose_spec.2.2.2

/-- The disc diagram of a planar map has one relator cell for each relator face. -/
theorem DiscDiagram.ofPlanar_rCellCount {W : Set (List (RelLetter G Lambda))}
    (M : CombMap.{v}) (hplanar : M.IsPlanar) (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d)) (outerFace : M.Face)
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face)
    (houter : outerFace ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W)
    (htriv : ∀ f, f ≠ outerFace → f ∉ relFaces →
      RelLetter.listVal ((faceBoundary f).darts.map label) = 1) :
    (DiscDiagram.ofPlanar (W := W) M hplanar label label_alpha outerFace faceBoundary
      relFaces houter hword htriv).rCellCount = relFaces.card := by
  classical
  obtain ⟨hnd, hiff, -, -⟩ := (exists_relatorCells_of_planar (W := W) M hplanar label
    label_alpha outerFace faceBoundary relFaces houter hword htriv).choose_spec
  have hfin : ((exists_relatorCells_of_planar (W := W) M hplanar label label_alpha outerFace
      faceBoundary relFaces houter hword htriv).choose.map RelatorCell.face).toFinset =
        relFaces := by
    ext f
    rw [List.mem_toFinset]
    exact hiff f
  have h1 := List.toFinset_card_of_nodup hnd
  rw [hfin, List.length_map] at h1
  exact h1.symm

/-- The disc diagram of a planar map reads the reverse-inverse of its outer face. -/
theorem DiscDiagram.ofPlanar_boundaryWord {W : Set (List (RelLetter G Lambda))}
    (M : CombMap.{v}) (hplanar : M.IsPlanar) (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d)) (outerFace : M.Face)
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face)
    (houter : outerFace ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W)
    (htriv : ∀ f, f ≠ outerFace → f ∉ relFaces →
      RelLetter.listVal ((faceBoundary f).darts.map label) = 1) :
    (DiscDiagram.ofPlanar (W := W) M hplanar label label_alpha outerFace faceBoundary
      relFaces houter hword htriv).boundaryWord =
        RelWord.revInv ((faceBoundary outerFace).darts.map label) :=
  rfl

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_relatorCells_of_planar
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.ofPlanar
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.ofPlanar_rCellCount
