import GroupApproximation.GGT.VanKampen.SurgeryOuterSpurThickening
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.Meta.AxiomGuard

/-!
# Thickening the edges between relator cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The cell pocket walk `s_1 t_1 s_2 t_2` of
two regions joining the cells `Π_i` and `Π_j` has no repeated dart and uses no edge in both
directions once the diagram satisfies the edge conditions `CellPocketWalk.CopyClean`
(`Estimating/OsinPocketCellCopyWalk.lean`).  Three of them concern relator cells alone: no edge has
`Π_i` on both sides, no edge has `Π_j` on both sides, and no edge joins `Π_j` to `Π_i`.  This file
gives all three at once, for every relator cell with at least two darts.  Configuration (b′) of the
multiple-edge pocket, a spur on `Π_i` between the arcs of the two regions, is such an edge.

A **cell-edge dart** is a dart of a relator face with at least two darts whose reverse lies on a
relator face.  The doubling of `FaceEdgeDoubling` along a cell-edge dart `w_j`, inside its relator
face `f`, inserts a G-cell digon `none, w_j` on the `f` side of the edge: `f` reads the old
traversal with the new dart in the place of `w_j`, whose reverse lies on the digon, and `w_j` now
lies on the digon (`FaceEdgeDoubling.faceOf_none_digon`, `faceOf_embed_dart_digon`).  Every other
old dart keeps its face and its reverse, and a relator face keeps its number of darts, so a
cell-edge dart of any doubled diagram is an old one other than `w_j` (`exists_of_isCellEdgeDart`),
and doubling a cell-edge dart lowers their number (`cellEdgeCount_lt`).  When no relator word has
value one, no region contains a relator face, so every region avoids `f` and the face across `w_j`
and transports with its face set, weight, target profile and source index (`sectionFamily`,
through `FaceEdgeDoubling.regionFamily`).  The model test is `SurgeryCellEdgeThickeningModel.lean`.

* `IsCellEdgeDart`, `cellEdgeCount`.
* `faceOf_embed_eq_faceImage`, `boundary_faceImage_length`: faces of the doubled map.
* `exists_of_isCellEdgeDart`, `cellEdgeCount_lt`, `relatorValue_ne_one`, `cell_avoid`.
* `regionFamilyEquiv`, `sectionFamily`, `exists_cellEdgeFree`.
* `CellEdgeThickeningStatement`, `cellEdgeThickening`: the closed statement.
* `cell_self_of_noCellEdgeDart`, `cell_cell_of_noCellEdgeDart`: the three edge conditions.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellEdgeThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Basics

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- A **cell-edge dart**: a dart of a relator face with at least two darts whose reverse lies on a
relator face. -/
def IsCellEdgeDart (Delta : DiscDiagram.{u, w, v} W) (x : Delta.toCombMap.Dart) : Prop :=
  1 < (Delta.faceBoundary (Delta.toCombMap.faceOf x)).darts.length ∧
    (∃ C ∈ Delta.relatorCells, C.face = Delta.toCombMap.faceOf x) ∧
      ∃ C ∈ Delta.relatorCells, C.face = Delta.toCombMap.faceOf (Delta.toCombMap.alpha x)

/-- The number of cell-edge darts. -/
noncomputable def cellEdgeCount (Delta : DiscDiagram.{u, w, v} W) : ℕ :=
  (Finset.univ.filter (IsCellEdgeDart Delta)).card

/-- Without cell-edge darts, no edge has a relator cell with at least two darts on both sides
(`CellPocketWalk.CopyClean.cell_self_first` and `cell_self_second`). -/
theorem cell_self_of_noCellEdgeDart {Delta : DiscDiagram.{u, w, v} W}
    (hno : ∀ x, ¬ IsCellEdgeDart Delta x) {k : Fin Delta.rCellCount}
    (hk : 1 < (cellDarts Delta k).length) :
    ∀ d, Delta.toCombMap.faceOf d = (cell Delta k).face →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠ (cell Delta k).face := by
  intro d hd hacross
  refine hno d ⟨?_, ⟨cell Delta k, cell_mem Delta k, hd.symm⟩,
    ⟨cell Delta k, cell_mem Delta k, hacross.symm⟩⟩
  rw [hd]
  exact hk

/-- Without cell-edge darts, no edge joins a relator cell with at least two darts to another
relator cell (`CellPocketWalk.CopyClean.cell_cell`). -/
theorem cell_cell_of_noCellEdgeDart {Delta : DiscDiagram.{u, w, v} W}
    (hno : ∀ x, ¬ IsCellEdgeDart Delta x) {k l : Fin Delta.rCellCount}
    (hl : 1 < (cellDarts Delta l).length) :
    ∀ d, Delta.toCombMap.faceOf d = (cell Delta l).face →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠ (cell Delta k).face := by
  intro d hd hacross
  refine hno d ⟨?_, ⟨cell Delta l, cell_mem Delta l, hd.symm⟩,
    ⟨cell Delta k, cell_mem Delta k, hacross.symm⟩⟩
  rw [hd]
  exact hl

end Basics

section Thickening

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- Every old dart other than the doubled one lies on the image of its face, by
`FaceEdgeDoubling.faceOf_embed_of_face_of_ne` and `faceOf_embed_of_face_ne`. -/
theorem faceOf_embed_eq_faceImage {y : Delta.toCombMap.Dart}
    (hy : y ≠ FaceEdgeDoubling.dart Delta f j) :
    (FaceEdgeDoubling.map Delta f j hlen).faceOf (embed Delta.toCombMap y) =
      FaceEdgeDoubling.faceImage Delta f j hlen (Delta.toCombMap.faceOf y) := by
  by_cases hg : Delta.toCombMap.faceOf y = f
  · rw [FaceEdgeDoubling.faceOf_embed_of_face_of_ne Delta f j hlen hg hy, hg,
      FaceEdgeDoubling.faceImage_self]
  · exact FaceEdgeDoubling.faceOf_embed_of_face_ne Delta f j hlen hg

/-- The traversal of the image of a face has as many darts as the old traversal. -/
theorem boundary_faceImage_length (g : Delta.toCombMap.Face) :
    (FaceEdgeDoubling.boundary Delta f j hlen
      (FaceEdgeDoubling.faceImage Delta f j hlen g)).darts.length =
      (Delta.faceBoundary g).darts.length := by
  simpa only [List.length_map] using
    congrArg List.length (FaceEdgeDoubling.boundary_faceImage_word Delta f j hlen g)

/-- **A cell-edge dart of the doubled diagram is an old cell-edge dart other than `w_j`.**  The new
dart of `f` has its reverse on the digon, the doubled dart lies on the digon, and the digon is no
relator cell.  This holds for the doubling along any dart of any inner face. -/
theorem exists_of_isCellEdgeDart
    {x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hx : IsCellEdgeDart (FaceEdgeDoubling.diagram Delta f j hlen hf) x) :
    ∃ d, embed Delta.toCombMap d = x ∧ IsCellEdgeDart Delta d ∧
      d ≠ FaceEdgeDoubling.dart Delta f j := by
  obtain ⟨hxlen, ⟨C, hC, hCf⟩, ⟨C', hC', hC'f⟩⟩ := hx
  have hCm : C ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hCm
  have hC'm : C' ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC'
  obtain ⟨C₁, hC₁, rfl⟩ := List.mem_map.mp hC'm
  change FaceEdgeDoubling.faceImage Delta f j hlen C₀.face =
    (FaceEdgeDoubling.map Delta f j hlen).faceOf x at hCf
  change FaceEdgeDoubling.faceImage Delta f j hlen C₁.face =
    (FaceEdgeDoubling.map Delta f j hlen).faceOf
      ((FaceEdgeDoubling.map Delta f j hlen).alpha x) at hC'f
  -- `x` is the image of an old dart of the face of `C₀` other than `w_j`.
  obtain ⟨d, hdx, hdface, hdne⟩ : ∃ d, embed Delta.toCombMap d = x ∧
      Delta.toCombMap.faceOf d = C₀.face ∧ d ≠ FaceEdgeDoubling.dart Delta f j := by
    have hxmem : x ∈ (FaceEdgeDoubling.boundary Delta f j hlen
        (FaceEdgeDoubling.faceImage Delta f j hlen C₀.face)).darts :=
      ((FaceEdgeDoubling.boundary Delta f j hlen _).mem_iff x).mpr hCf.symm
    by_cases hg : C₀.face = f
    · rw [hg, FaceEdgeDoubling.faceImage_self, FaceEdgeDoubling.boundary_cellFace_darts] at hxmem
      obtain ⟨d, hd, hdx⟩ := List.mem_map.mp hxmem
      by_cases hdd : d = FaceEdgeDoubling.dart Delta f j
      · rw [FaceEdgeDoubling.dartImage, if_pos hdd] at hdx
        subst hdx
        change FaceEdgeDoubling.faceImage Delta f j hlen C₁.face =
          (FaceEdgeDoubling.map Delta f j hlen).faceOf none at hC'f
        rw [FaceEdgeDoubling.faceOf_none_digon] at hC'f
        exact (FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen C₁.face hC'f).elim
      · rw [FaceEdgeDoubling.dartImage, if_neg hdd] at hdx
        exact ⟨d, hdx, (((Delta.faceBoundary f).mem_iff d).mp hd).trans hg.symm, hdd⟩
    · rw [FaceEdgeDoubling.faceImage_of_ne Delta f j hlen hg,
        FaceEdgeDoubling.boundary_kept Delta f j hlen hg] at hxmem
      obtain ⟨d, hd, hdx⟩ := List.mem_map.mp hxmem
      have hdface := ((Delta.faceBoundary C₀.face).mem_iff d).mp hd
      refine ⟨d, hdx, hdface, fun hdd => hg ?_⟩
      rw [← hdface, hdd, FaceEdgeDoubling.dart_face]
  subst hdx
  change FaceEdgeDoubling.faceImage Delta f j hlen C₁.face =
    (FaceEdgeDoubling.map Delta f j hlen).faceOf
      (embed Delta.toCombMap (Delta.toCombMap.alpha d)) at hC'f
  by_cases had : Delta.toCombMap.alpha d = FaceEdgeDoubling.dart Delta f j
  · rw [had, FaceEdgeDoubling.faceOf_embed_dart_digon] at hC'f
    exact (FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen C₁.face hC'f).elim
  · rw [faceOf_embed_eq_faceImage Delta f j hlen had] at hC'f
    have h2 : 1 < (FaceEdgeDoubling.boundary Delta f j hlen
        ((FaceEdgeDoubling.map Delta f j hlen).faceOf (embed Delta.toCombMap d))).darts.length :=
      hxlen
    rw [faceOf_embed_eq_faceImage Delta f j hlen hdne, boundary_faceImage_length] at h2
    exact ⟨d, rfl, ⟨h2, ⟨C₀, hC₀, hdface.symm⟩,
      ⟨C₁, hC₁, FaceEdgeDoubling.faceImage_injective Delta f j hlen hC'f⟩⟩, hdne⟩

/-- **Thickening a cell-edge dart removes it and creates none.** -/
theorem cellEdgeCount_lt (hcell : IsCellEdgeDart Delta (FaceEdgeDoubling.dart Delta f j)) :
    cellEdgeCount (FaceEdgeDoubling.diagram Delta f j hlen hf) < cellEdgeCount Delta := by
  have hmem : FaceEdgeDoubling.dart Delta f j ∈ Finset.univ.filter (IsCellEdgeDart Delta) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩
  unfold cellEdgeCount
  refine lt_of_le_of_lt ?_ (Finset.card_erase_lt_of_mem hmem)
  refine Finset.card_le_card_of_injOn
    (fun x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart =>
      (Option.bind x id).getD (FaceEdgeDoubling.dart Delta f j)) ?_ ?_
  · intro x hx
    obtain ⟨d, rfl, hd, hne⟩ :=
      exists_of_isCellEdgeDart Delta f j hlen hf (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    exact Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩)
  · intro x hx y hy hxy
    obtain ⟨d, rfl, -, -⟩ :=
      exists_of_isCellEdgeDart Delta f j hlen hf (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    obtain ⟨e, rfl, -, -⟩ :=
      exists_of_isCellEdgeDart Delta f j hlen hf (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    exact congrArg (embed Delta.toCombMap) hxy

/-- The relator words are unchanged. -/
theorem relatorValue_ne_one (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1) :
    ∀ C ∈ (FaceEdgeDoubling.diagram Delta f j hlen hf).relatorCells,
      RelLetter.listVal C.word ≠ 1 := by
  intro C hC
  have hC' : C ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC'
  exact hvalue C₀ hC₀

/-- When no relator word has value one, no region contains the relator face of a cell-edge dart
or the relator face across it. -/
theorem cell_avoid {D : RelGenSet G Lambda} {eps : ℕ}
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hcell : IsCellEdgeDart Delta (FaceEdgeDoubling.dart Delta f j))
    (family : Finset (RegionCandidate D eps Delta)) :
    ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1 := by
  have hno : ∀ (a : RegionCandidate D eps Delta) (C : RelatorCell Delta.toCombMap Delta.outerFace W),
      C ∈ Delta.relatorCells → C.face ∉ a.1 := by
    intro a C hC hmem
    have hone := (a.2.boundary.all_gCells _ hmem).2
    apply hvalue C hC
    rw [Delta.relatorCell_word C hC]
    exact hone
  intro a _
  obtain ⟨-, ⟨C, hC, hCf⟩, ⟨C', hC', hC'f⟩⟩ := hcell
  refine ⟨fun hmem => hno a C hC ?_, fun hmem => hno a C' hC' ?_⟩
  · rw [hCf, FaceEdgeDoubling.dart_face]
    exact hmem
  · rw [hC'f]
    exact hmem

/-- The retained family, as an equivalence onto the transported family. -/
noncomputable def regionFamilyEquiv {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1) :
    family ≃ FaceEdgeDoubling.regionFamily Delta f j hlen hf family havoid :=
  Equiv.ofBijective (fun a => ⟨FaceEdgeDoubling.regionFamilyEmbedding Delta f j hlen hf family
      havoid a, Finset.mem_map_of_mem _ (Finset.mem_attach family a)⟩)
    (And.intro (fun a b h => (FaceEdgeDoubling.regionFamilyEmbedding Delta f j hlen hf family
        havoid).injective (congrArg Subtype.val h))
      (fun x => by
        obtain ⟨a, _, ha⟩ := Finset.mem_map.mp x.property
        exact ⟨a, Subtype.ext ha⟩))

theorem regionFamilyEquiv_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    (a : family) :
    RegionCandidate.SameTargetProfile (regionFamilyEquiv Delta f j hlen hf family havoid a).1
      a.1 :=
  FaceEdgeDoubling.regionCandidate_profile Delta f j hlen hf ⟨a.val, havoid a.val a.property⟩

theorem regionFamilyEquiv_source {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    (a : family) :
    (regionFamilyEquiv Delta f j hlen hf family havoid a).1.2.source.val = a.1.2.source.val :=
  rfl

end Thickening

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A distinguished section family across the doubling of an edge of a face** that no region
contains, along a dart whose opposite face no region contains.  The weight and the number of
regions are unchanged and the labels stay legal, so the transported family is again optimal. -/
noncomputable def sectionFamily (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1) :
    GloballyDistinguishedSectionFamily D lambda c eps Delta cuts where
  diagram := FaceEdgeDoubling.diagram S.diagram f j hlen hf
  equiv := S.equiv.trans (FaceEdgeDoubling.oEquivalent S.diagram f j hlen hf)
  reduced := FaceEdgeDoubling.reduced S.diagram f j hlen hf S.reduced
  family := FaceEdgeDoubling.regionFamily S.diagram f j hlen hf S.family havoid
  pairwise :=
    FaceEdgeDoubling.regionFamily_pairwise S.diagram f j hlen hf S.family havoid S.pairwise
  respects := by
    intro a ha
    obtain ⟨b, hb, hab⟩ :=
      FaceEdgeDoubling.regionFamily_profile S.diagram f j hlen hf S.family havoid ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab
      (FaceEdgeDoubling.regionFamily_noLoop S.diagram f j hlen hf S.family havoid
        (fun x hx => (S.respects x hx).1) ha)
      (S.respects b hb)
  nondegenerate := by
    intro a ha
    obtain ⟨b, hb, hab⟩ :=
      FaceEdgeDoubling.regionFamily_profile S.diagram f j hlen hf S.family havoid ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b hb
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩
  label_admissible :=
    FaceEdgeDoubling.label_admissible S.diagram f j hlen hf (symmetricLabelAlphabet D)
      (symmetricLabelAlphabet.symmetric D) S.label_admissible
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (FaceEdgeDoubling.regionFamily_weight S.diagram f j hlen hf S.family havoid).symm
  card_minimal other hother hweight :=
    (FaceEdgeDoubling.regionFamily_card S.diagram f j hlen hf S.family havoid).trans_le
      (S.card_minimal other hother (hweight.trans
        (FaceEdgeDoubling.regionFamily_weight S.diagram f j hlen hf S.family havoid)))

/-- **Induction on the number of cell-edge darts, carrying an invariant**, and keeping the absence of
relator words of value one.  Every property of distinguished section families that one doubling
step `sectionFamily` preserves also holds for the output. -/
theorem exists_cellEdgeFree_of_invariant
    (P : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts → Prop)
    (hP : ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
      (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1),
      P S → P (sectionFamily S f j hlen hf havoid))
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) (hS : P S) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsCellEdgeDart S'.diagram x) ∧
          (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
            S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
              (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                (e a).1.2.source.val = a.1.2.source.val) ∧ P S' := by
  revert hvalue hS
  generalize hn : cellEdgeCount S.diagram = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hvalue hS
    by_cases hcell : ∃ x, IsCellEdgeDart S.diagram x
    · obtain ⟨x, hx⟩ := hcell
      have hlen : 1 < (S.diagram.faceBoundary (S.diagram.toCombMap.faceOf x)).darts.length :=
        hx.1
      obtain ⟨C, -, hCf⟩ := hx.2.1
      have hf : S.diagram.toCombMap.faceOf x ≠ S.diagram.outerFace := by
        rw [← hCf]
        exact C.face_ne_outer
      obtain ⟨j, hj⟩ := List.get_of_mem
        (((S.diagram.faceBoundary (S.diagram.toCombMap.faceOf x)).mem_iff x).mpr rfl)
      have hcell2 : IsCellEdgeDart S.diagram
          (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j) := by
        rw [FaceEdgeDoubling.dart_eq_get, hj]
        exact hx
      have havoid := cell_avoid S.diagram _ j hvalue hcell2 S.family
      obtain ⟨S', e, ⟨equiv'⟩, hfree', hvalue', hweight, hprofile, hPS'⟩ :=
        ih _ (lt_of_lt_of_eq (cellEdgeCount_lt S.diagram _ j hlen hf hcell2) hn)
          (sectionFamily S _ j hlen hf havoid) rfl
          (relatorValue_ne_one S.diagram _ j hlen hf hvalue) (hP S _ j hlen hf havoid hS)
      refine ⟨S', (regionFamilyEquiv S.diagram _ j hlen hf S.family havoid).trans e,
        ⟨(FaceEdgeDoubling.oEquivalent S.diagram _ j hlen hf).trans equiv'⟩, hfree', hvalue',
        hweight.trans
          (FaceEdgeDoubling.regionFamily_weight S.diagram _ j hlen hf S.family havoid),
        fun a => ?_, hPS'⟩
      obtain ⟨hprof, hsource⟩ :=
        hprofile (regionFamilyEquiv S.diagram _ j hlen hf S.family havoid a)
      exact And.intro
        (hprof.trans (regionFamilyEquiv_profile S.diagram _ j hlen hf S.family havoid a))
        (hsource.trans (regionFamilyEquiv_source S.diagram _ j hlen hf S.family havoid a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, fun x hx => hcell ⟨x, hx⟩,
        hvalue, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl, hS⟩

/-- **Induction on the number of cell-edge darts**, keeping the absence of relator words of value
one. -/
theorem exists_cellEdgeFree (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsCellEdgeDart S'.diagram x) ∧
          (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
            S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
              ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                (e a).1.2.source.val = a.1.2.source.val := by
  obtain ⟨S', e, hequiv, hfree, hvalue', hweight, hprofile, -⟩ :=
    exists_cellEdgeFree_of_invariant (fun _ => True) (fun _ _ _ _ _ _ _ => trivial) S hvalue
      trivial
  exact ⟨S', e, hequiv, hfree, hvalue', hweight, hprofile⟩

end Family

/-- **Cell-edge thickening.**  A distinguished section family with no relator word of value one
has a distinguished section family over the same cuts whose diagram is O-equivalent to the old one
and has no edge with a relator face of at least two darts on one side and a relator face on the
other.  No relator word of the new diagram has value one.  Its regions correspond bijectively to
the old ones, with the same total weight, and every region keeps its target profile and the index
of its source cell. -/
def CellEdgeThickeningStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
      ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        (e : S.family ≃ S'.family),
        Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
          (∀ x, ¬ IsCellEdgeDart S'.diagram x) ∧
            (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
              S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                  (e a).1.2.source.val = a.1.2.source.val

theorem cellEdgeThickening : CellEdgeThickeningStatement.{u, w, v} := by
  unfold CellEdgeThickeningStatement
  intro _ _ _ _ _ _ _ _ _ _ S hvalue
  exact exists_cellEdgeFree S hvalue

end GroupApproximation.GGT.VanKampen.CellEdgeThickening

#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.cellEdgeThickening
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.cell_self_of_noCellEdgeDart
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.cell_cell_of_noCellEdgeDart
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.faceOf_embed_eq_faceImage
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.boundary_faceImage_length
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.exists_of_isCellEdgeDart
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.cellEdgeCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.relatorValue_ne_one
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.cell_avoid
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.regionFamilyEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.sectionFamily
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.exists_cellEdgeFree_of_invariant
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeThickening.exists_cellEdgeFree
