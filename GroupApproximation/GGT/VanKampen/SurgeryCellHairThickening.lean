import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.GGT.VanKampen.SurgeryHairOpening
import GroupApproximation.Meta.AxiomGuard

/-!
# Opening the hairs of relator cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The pocket walk `s_1 t_1 s_2 t_2` of
two exterior regions of a cell `Π` is the boundary cycle of a pocket face set once the diagram
satisfies the edge conditions `PocketWalk.CopyClean` (`Estimating/OsinPocketCopyWalk`).  One of
them is that no edge has `Π` on both sides (`cell_self`).  `OuterCellThickening` gives the two
conditions on the exterior, `spur` and `cell_outer`.  This file gives `cell_self` for every
relator cell, keeping both of those.

A cell hair is an edge with one relator cell on both sides.  The doubling of
`FaceEdgeDoubling.diagram` along a cell hair `w_j` of the face `f` inserts a G-cell digon
`none, w_j` inside `f`: `w_j` now lies on the digon, its reverse stays on `f`, and the new dart
of `f` has the digon across it.  Every other dart keeps its face through `faceImage`, and the
exterior traversal is the old one through `embed`.  So the number of cell hairs drops by one
(`cellHairCount_lt`), and no outer spur and no outer cell dart appears (`noOuterSpur`,
`noOuterCellDart`).  When no relator word has value one, no region contains a relator cell, so
`HairOpening.sectionFamily` carries the family across with its weight, target profiles and
source cells.

* `IsCellHair`, `cellHairCount`.
* `cell_self_of_noCellHair`: the edge condition `CopyClean.cell_self`, for every source cell.
* `exists_of_isCellHair`: a cell hair of the doubled diagram is an old one other than `w_j`.
* `exists_cellHairFree`: induction on the number of cell hairs.
* `CellHairThickeningStatement`, `cellHairThickening`: from a distinguished section family with
  no outer spur, no outer cell dart and no relator word of value one.
* `OuterCellHairThickeningStatement`, `outerCellHairThickening`: composed with
  `OuterCellThickening.outerCellThickening`, from any distinguished section family over a boundary
  of length at least two with no relator word of value one.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellHairThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Basics

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- A **cell hair**: a dart whose edge has one relator cell on both sides. -/
def IsCellHair (Delta : DiscDiagram.{u, w, v} W) (x : Delta.toCombMap.Dart) : Prop :=
  HairOpening.IsHair Delta x ∧ ∃ C ∈ Delta.relatorCells, C.face = Delta.toCombMap.faceOf x

/-- The number of cell hair darts. -/
noncomputable def cellHairCount (Delta : DiscDiagram.{u, w, v} W) : ℕ :=
  (Finset.univ.filter (IsCellHair Delta)).card

/-- Without cell hairs, no edge has a relator cell on both sides (`CopyClean.cell_self`, for
every source cell). -/
theorem cell_self_of_noCellHair {Delta : DiscDiagram.{u, w, v} W}
    (hno : ∀ x, ¬ IsCellHair Delta x) (i : Fin Delta.rCellCount) :
    ∀ d, Delta.toCombMap.faceOf d = (Embedded.cell Delta i).face →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠ (Embedded.cell Delta i).face := by
  intro d hd hal
  exact hno d ⟨hd.trans hal.symm, Embedded.cell Delta i, Embedded.cell_mem Delta i, hd.symm⟩

/-- When no relator word has value one, no region contains a relator cell. -/
theorem relatorFace_not_mem {Delta : DiscDiagram.{u, w, v} W} {D : RelGenSet G Lambda} {eps : ℕ}
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1)
    {C : RelatorCell Delta.toCombMap Delta.outerFace W} (hC : C ∈ Delta.relatorCells)
    (a : RegionCandidate D eps Delta) : C.face ∉ a.1 := by
  intro hmem
  have hone := (a.2.boundary.all_gCells _ hmem).2
  apply hvalue C hC
  rw [Delta.relatorCell_word C hC]
  exact hone

end Basics

section Doubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- The first new dart lies on the digon. -/
theorem faceOf_none :
    (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf none =
      FaceEdgeDoubling.digon Delta f j hlen := by
  apply ((FaceEdgeDoubling.boundary Delta f j hlen
    (FaceEdgeDoubling.digon Delta f j hlen)).mem_iff _).mp
  rw [FaceEdgeDoubling.boundary_digon]
  exact List.mem_cons.mpr (Or.inl rfl)

/-- The doubled dart lies on the digon. -/
theorem faceOf_embed_dart :
    (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf
        (embed Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) =
      FaceEdgeDoubling.digon Delta f j hlen := by
  apply ((FaceEdgeDoubling.boundary Delta f j hlen
    (FaceEdgeDoubling.digon Delta f j hlen)).mem_iff _).mp
  rw [FaceEdgeDoubling.boundary_digon]
  exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- Every old dart other than the doubled one keeps its face. -/
theorem faceOf_embed {y : Delta.toCombMap.Dart} (hy : y ≠ FaceEdgeDoubling.dart Delta f j) :
    (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf (embed Delta.toCombMap y) =
      FaceEdgeDoubling.faceImage Delta f j hlen (Delta.toCombMap.faceOf y) := by
  by_cases hg : Delta.toCombMap.faceOf y = f
  · rw [hg, FaceEdgeDoubling.faceImage_self]
    apply ((FaceEdgeDoubling.boundary Delta f j hlen
      (FaceEdgeDoubling.cellFace Delta f j hlen)).mem_iff _).mp
    rw [FaceEdgeDoubling.boundary_cellFace_darts]
    refine List.mem_map.mpr ⟨y, ((Delta.faceBoundary f).mem_iff y).mpr hg, ?_⟩
    rw [FaceEdgeDoubling.dartImage, if_neg hy]
  · rw [FaceEdgeDoubling.faceImage_of_ne Delta f j hlen hg]
    apply ((FaceEdgeDoubling.boundary Delta f j hlen
      (FaceEdgeDoubling.keep Delta f j hlen (Delta.toCombMap.faceOf y))).mem_iff _).mp
    rw [FaceEdgeDoubling.boundary_kept Delta f j hlen hg]
    exact List.mem_map.mpr ⟨y, ((Delta.faceBoundary _).mem_iff y).mpr rfl, rfl⟩

/-- The dart map onto the face of `f` never gives the first new dart. -/
theorem dartImage_ne_none (e : Delta.toCombMap.Dart) :
    FaceEdgeDoubling.dartImage Delta f j hlen e ≠ none := by
  unfold FaceEdgeDoubling.dartImage
  split_ifs <;> exact Option.some_ne_none _

/-- A dart of a retained face other than `f` is an old dart of that face. -/
theorem exists_of_faceOf_eq_keep {g : Delta.toCombMap.Face} (hg : g ≠ f)
    {x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hx : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
      FaceEdgeDoubling.keep Delta f j hlen g) :
    ∃ d, Delta.toCombMap.faceOf d = g ∧ embed Delta.toCombMap d = x := by
  have hmem := ((FaceEdgeDoubling.boundary Delta f j hlen
    (FaceEdgeDoubling.keep Delta f j hlen g)).mem_iff x).mpr hx
  rw [FaceEdgeDoubling.boundary_kept Delta f j hlen hg] at hmem
  obtain ⟨d, hd, hdx⟩ := List.mem_map.mp hmem
  exact ⟨d, ((Delta.faceBoundary g).mem_iff d).mp hd, hdx⟩

/-- A dart of the face of `f` is the image of an old dart of `f`. -/
theorem exists_of_faceOf_eq_cellFace
    {x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hx : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
      FaceEdgeDoubling.cellFace Delta f j hlen) :
    ∃ d, Delta.toCombMap.faceOf d = f ∧ FaceEdgeDoubling.dartImage Delta f j hlen d = x := by
  have hmem := ((FaceEdgeDoubling.boundary Delta f j hlen
    (FaceEdgeDoubling.cellFace Delta f j hlen)).mem_iff x).mpr hx
  rw [FaceEdgeDoubling.boundary_cellFace_darts, List.mem_map] at hmem
  obtain ⟨d, hd, hdx⟩ := hmem
  exact ⟨d, ((Delta.faceBoundary f).mem_iff d).mp hd, hdx⟩

/-- The exterior of the doubled diagram consists of the images of the old exterior darts. -/
theorem exists_of_faceOf_eq_outer
    {x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hx : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
      (FaceEdgeDoubling.diagram Delta f j hlen hf).outerFace) :
    ∃ d, Delta.toCombMap.faceOf d = Delta.outerFace ∧ embed Delta.toCombMap d = x :=
  exists_of_faceOf_eq_keep Delta f j hlen hf (Ne.symm hf) hx

/-- **A cell hair of the doubled diagram is an old cell hair other than `w_j`.**  The new dart
of `f` and `w_j` both have the digon across them, and the digon is no relator cell. -/
theorem exists_of_isCellHair {x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hx : IsCellHair (FaceEdgeDoubling.diagram Delta f j hlen hf) x) :
    ∃ d, embed Delta.toCombMap d = x ∧ IsCellHair Delta d ∧
      d ≠ FaceEdgeDoubling.dart Delta f j := by
  obtain ⟨hhair, C, hC, hCf⟩ := hx
  have hh : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
      (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf
        ((FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha x) := hhair
  have hC' : C ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC'
  have hface : FaceEdgeDoubling.faceImage Delta f j hlen C₀.face =
      (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x := hCf
  by_cases hg : C₀.face = f
  · rw [hg, FaceEdgeDoubling.faceImage_self] at hface
    obtain ⟨d, hd, hdx⟩ := exists_of_faceOf_eq_cellFace Delta f j hlen hf hface.symm
    obtain ⟨e, he, hex⟩ :=
      exists_of_faceOf_eq_cellFace Delta f j hlen hf (hh.symm.trans hface.symm)
    by_cases hdd : d = FaceEdgeDoubling.dart Delta f j
    · rw [FaceEdgeDoubling.dartImage, if_pos hdd] at hdx
      subst hdx
      change FaceEdgeDoubling.dartImage Delta f j hlen e = none at hex
      exact (dartImage_ne_none Delta f j hlen e hex).elim
    · rw [FaceEdgeDoubling.dartImage, if_neg hdd] at hdx
      subst hdx
      by_cases hee : e = FaceEdgeDoubling.dart Delta f j
      · rw [FaceEdgeDoubling.dartImage, if_pos hee] at hex
        change (some none : Option (Option Delta.toCombMap.Dart)) =
          some (some (Delta.toCombMap.alpha d)) at hex
        exact (Option.some_ne_none _ (Option.some.inj hex).symm).elim
      · rw [FaceEdgeDoubling.dartImage, if_neg hee] at hex
        change embed Delta.toCombMap e = embed Delta.toCombMap (Delta.toCombMap.alpha d) at hex
        have hea : e = Delta.toCombMap.alpha d := embed_injective Delta.toCombMap hex
        subst hea
        exact ⟨d, rfl, ⟨hd.trans he.symm, C₀, hC₀, hg.trans hd.symm⟩, hdd⟩
  · rw [FaceEdgeDoubling.faceImage_of_ne Delta f j hlen hg] at hface
    obtain ⟨d, hd, hdx⟩ := exists_of_faceOf_eq_keep Delta f j hlen hf hg hface.symm
    obtain ⟨e, he, hex⟩ :=
      exists_of_faceOf_eq_keep Delta f j hlen hf hg (hh.symm.trans hface.symm)
    subst hdx
    change embed Delta.toCombMap e = embed Delta.toCombMap (Delta.toCombMap.alpha d) at hex
    have hea : e = Delta.toCombMap.alpha d := embed_injective Delta.toCombMap hex
    subst hea
    have hdd : d ≠ FaceEdgeDoubling.dart Delta f j := by
      intro h
      apply hg
      rw [← hd, h]
      exact FaceEdgeDoubling.dart_face Delta f j
    exact ⟨d, rfl, ⟨hd.trans he.symm, C₀, hC₀, hd.symm⟩, hdd⟩

/-- **Opening a cell hair removes it and creates none.** -/
theorem cellHairCount_lt (hcell : IsCellHair Delta (FaceEdgeDoubling.dart Delta f j)) :
    cellHairCount (FaceEdgeDoubling.diagram Delta f j hlen hf) < cellHairCount Delta := by
  have hmem : FaceEdgeDoubling.dart Delta f j ∈ Finset.univ.filter (IsCellHair Delta) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩
  unfold cellHairCount
  refine lt_of_le_of_lt ?_ (Finset.card_erase_lt_of_mem hmem)
  refine Finset.card_le_card_of_injOn
    (fun x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart =>
      (Option.bind x id).getD (FaceEdgeDoubling.dart Delta f j)) ?_ ?_
  · intro x hx
    obtain ⟨d, rfl, hd, hne⟩ :=
      exists_of_isCellHair Delta f j hlen hf (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    exact Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩)
  · intro x hx y hy hxy
    obtain ⟨d, rfl, -, -⟩ :=
      exists_of_isCellHair Delta f j hlen hf (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    obtain ⟨e, rfl, -, -⟩ :=
      exists_of_isCellHair Delta f j hlen hf (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    exact congrArg (embed Delta.toCombMap) hxy

/-- An inner doubling creates no outer spur. -/
theorem noOuterSpur (hfree : ∀ x, ¬ OuterSpurThickening.IsOuterSpur Delta x) :
    ∀ x, ¬ OuterSpurThickening.IsOuterSpur (FaceEdgeDoubling.diagram Delta f j hlen hf) x := by
  intro x hx
  obtain ⟨d, hd, hdx⟩ := exists_of_faceOf_eq_outer Delta f j hlen hf hx.1
  subst hdx
  obtain ⟨e, he, hex⟩ := exists_of_faceOf_eq_outer Delta f j hlen hf hx.2
  change embed Delta.toCombMap e = embed Delta.toCombMap (Delta.toCombMap.alpha d) at hex
  have hea : e = Delta.toCombMap.alpha d := embed_injective Delta.toCombMap hex
  subst hea
  exact hfree d ⟨hd, he⟩

/-- An inner doubling creates no outer cell dart. -/
theorem noOuterCellDart (hfree : ∀ x, ¬ OuterCellThickening.IsOuterCellDart Delta x) :
    ∀ x, ¬ OuterCellThickening.IsOuterCellDart
      (FaceEdgeDoubling.diagram Delta f j hlen hf) x := by
  intro x hx
  obtain ⟨d, hd, hdx⟩ := exists_of_faceOf_eq_outer Delta f j hlen hf hx.1
  subst hdx
  obtain ⟨C, hC, hCf⟩ := hx.2
  have hC' : C ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC'
  have hface : FaceEdgeDoubling.faceImage Delta f j hlen C₀.face =
      (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf
        (embed Delta.toCombMap (Delta.toCombMap.alpha d)) := hCf
  by_cases had : Delta.toCombMap.alpha d = FaceEdgeDoubling.dart Delta f j
  · rw [had, faceOf_embed_dart Delta f j hlen hf] at hface
    exact FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen C₀.face hface
  · rw [faceOf_embed Delta f j hlen hf had] at hface
    exact hfree d ⟨hd, C₀, hC₀, FaceEdgeDoubling.faceImage_injective Delta f j hlen hface⟩

/-- The relator words are unchanged. -/
theorem relatorValue_ne_one
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1) :
    ∀ C ∈ (FaceEdgeDoubling.diagram Delta f j hlen hf).relatorCells,
      RelLetter.listVal C.word ≠ 1 := by
  intro C hC
  have hC' : C ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC'
  exact hvalue C₀ hC₀

end Doubling

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Induction on the number of cell hairs**, keeping the absence of outer spurs, of outer cell
darts and of relator words of value one. -/
theorem exists_cellHairFree (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hspur : ∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x)
    (hcell : ∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
          (∀ x, ¬ OuterCellThickening.IsOuterCellDart S'.diagram x) ∧
            (∀ x, ¬ IsCellHair S'.diagram x) ∧
              (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                  ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                    (e a).1.2.source.val = a.1.2.source.val := by
  revert hvalue hspur hcell
  generalize hn : cellHairCount S.diagram = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hvalue hspur hcell
    by_cases hhair : ∃ x, IsCellHair S.diagram x
    · obtain ⟨x, hx⟩ := hhair
      obtain ⟨j, hj⟩ := HairOpening.exists_dart_eq x
      have hlen := HairOpening.one_lt_length_of_isHair hx.1
      have hh : S.diagram.toCombMap.faceOf x =
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) := hx.1
      obtain ⟨C, hC, hCf⟩ := hx.2
      have hf : S.diagram.toCombMap.faceOf x ≠ S.diagram.outerFace := by
        rw [← hCf]
        exact C.face_ne_outer
      have hcell2 :
          IsCellHair S.diagram (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j) := by
        rw [hj]
        exact hx
      have havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf x ∉ a.1 ∧
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
            (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j)) ∉ a.1 := by
        intro a _
        have hnot := relatorFace_not_mem hvalue hC a
        rw [hCf] at hnot
        refine ⟨hnot, ?_⟩
        rw [hj, ← hh]
        exact hnot
      obtain ⟨S', e, ⟨equiv'⟩, hspur', hcell', hhair', hvalue', hweight, hprofile⟩ :=
        ih _ (lt_of_lt_of_eq (cellHairCount_lt S.diagram _ j hlen hf hcell2) hn)
          (HairOpening.sectionFamily S _ j hlen hf havoid) rfl
          (relatorValue_ne_one S.diagram _ j hlen hf hvalue)
          (noOuterSpur S.diagram _ j hlen hf hspur)
          (noOuterCellDart S.diagram _ j hlen hf hcell)
      refine ⟨S', (HairOpening.regionFamilyEquiv S.diagram _ j hlen hf S.family havoid).trans e,
        ⟨(FaceEdgeDoubling.oEquivalent S.diagram _ j hlen hf).trans equiv'⟩, hspur', hcell',
        hhair', hvalue',
        hweight.trans (FaceEdgeDoubling.regionFamily_weight S.diagram _ j hlen hf S.family havoid),
        fun a => ?_⟩
      obtain ⟨hprof, hsource⟩ :=
        hprofile (HairOpening.regionFamilyEquiv S.diagram _ j hlen hf S.family havoid a)
      exact And.intro
        (hprof.trans
          (HairOpening.regionFamilyEquiv_profile S.diagram _ j hlen hf S.family havoid a))
        (hsource.trans
          (HairOpening.regionFamilyEquiv_source S.diagram _ j hlen hf S.family havoid a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, hspur, hcell,
        fun x hx => hhair ⟨x, hx⟩, hvalue, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl⟩

end Family

/-- **Cell hair thickening.**  A distinguished section family whose diagram has no outer spur,
no edge between a relator cell and the exterior, and no relator word of value one has a
distinguished section family over the same cuts whose diagram is O-equivalent to the old one,
keeps those three properties, and has no edge with one relator cell on both sides.  Its regions
correspond bijectively to the old ones, with the same total weight, and every region keeps its
target profile and the index of its source cell. -/
def CellHairThickeningStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    (∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x) →
      (∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x) →
        (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
          ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
            (e : S.family ≃ S'.family),
            Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
              (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
                (∀ x, ¬ OuterCellThickening.IsOuterCellDart S'.diagram x) ∧
                  (∀ x, ¬ IsCellHair S'.diagram x) ∧
                    (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                      S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                        ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                          (e a).1.2.source.val = a.1.2.source.val

theorem cellHairThickening : CellHairThickeningStatement.{u, w, v} := by
  unfold CellHairThickeningStatement
  intro _ _ _ D lambda c eps W Delta cuts S hspur hcell hvalue
  exact exists_cellHairFree S hvalue hspur hcell

/-- **Outer cell and cell hair thickening.**  A distinguished section family over a boundary
word of length at least two, with no relator word of value one, has a distinguished section
family over the same cuts whose diagram is O-equivalent to the old one, has no outer spur, no
edge between a relator cell and the exterior, and no edge with one relator cell on both sides,
and still has no relator word of value one.  Its regions correspond bijectively to the old ones,
with the same total weight, and every region keeps its target profile and the index of its source
cell.  With `OuterCellThickening.spur_of_noOuterSpur`,
`OuterCellThickening.cell_outer_of_noOuterCellDart` and `cell_self_of_noCellHair`, the new
diagram satisfies the conditions `spur`, `cell_outer` and `cell_self` of `PocketWalk.CopyClean`
for every pocket walk. -/
def OuterCellHairThickeningStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    1 < Delta.boundaryWord.length →
      (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
        ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
          (e : S.family ≃ S'.family),
          Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
            (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
              (∀ x, ¬ OuterCellThickening.IsOuterCellDart S'.diagram x) ∧
                (∀ x, ¬ IsCellHair S'.diagram x) ∧
                  (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                    S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                      ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                        (e a).1.2.source.val = a.1.2.source.val

theorem outerCellHairThickening : OuterCellHairThickeningStatement.{u, w, v} := by
  unfold OuterCellHairThickeningStatement
  intro _ _ _ D lambda c eps W Delta cuts S hlen0 hvalue
  obtain ⟨S₁, e₁, ⟨equiv₁⟩, hspur₁, hcell₁, hvalue₁, hweight₁, hprofile₁⟩ :=
    OuterCellThickening.outerCellThickening D lambda c eps W Delta cuts S hlen0 hvalue
  obtain ⟨S₂, e₂, ⟨equiv₂⟩, hspur₂, hcell₂, hhair₂, hvalue₂, hweight₂, hprofile₂⟩ :=
    exists_cellHairFree S₁ hvalue₁ hspur₁ hcell₁
  refine ⟨S₂, e₁.trans e₂, ⟨equiv₁.trans equiv₂⟩, hspur₂, hcell₂, hhair₂, hvalue₂,
    hweight₂.trans hweight₁, fun a => ?_⟩
  obtain ⟨hprof₂, hsource₂⟩ := hprofile₂ (e₁ a)
  obtain ⟨hprof₁, hsource₁⟩ := hprofile₁ a
  exact And.intro (hprof₂.trans hprof₁) (hsource₂.trans hsource₁)

end GroupApproximation.GGT.VanKampen.CellHairThickening

#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.cellHairThickening
#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.outerCellHairThickening
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.cell_self_of_noCellHair
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.relatorFace_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.exists_of_isCellHair
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.cellHairCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.noOuterSpur
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.noOuterCellDart
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.relatorValue_ne_one
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.exists_cellHairFree
