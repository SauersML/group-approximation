import GroupApproximation.GGT.VanKampen.SurgeryOuterSpurThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# Thickening the edges between relator cells and the exterior

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The pocket walk `s_1 t_1 s_2 t_2` of
two exterior regions of a cell `Π` is the boundary cycle of a pocket face set once the diagram
satisfies the edge conditions `PocketWalk.CopyClean` (`Estimating/OsinPocketCopyWalk`).  Two of
them concern the exterior: no edge has the exterior on both sides (`spur`), and no edge joins
`Π` to the exterior (`cell_outer`).  `OuterSpurThickening` gives the first.  This file gives
both at once, for every relator cell.

Let `w_j` be a dart of the exterior whose reverse lies on a relator cell.  The doubling of
`FaceEdgeDoubling` along `w_j` inserts a G-cell digon `none, w_j` between the cell and the
exterior: the exterior reads the old traversal with the new dart in the place of `w_j`, whose
reverse lies on the digon.  Every other exterior dart keeps its reverse, so the number of outer
cell darts drops by one (`outerCellCount_lt`), and no outer spur is created
(`OuterSpurThickening.exists_of_isOuterSpur`).  When no relator word has value one, no region
contains a relator cell, so every region avoids the face across `w_j` and transports with its
face set, weight, target profile and source index (`sectionFamilyOfAvoid`).

* `IsOuterCellDart`: a dart of the exterior whose reverse lies on a relator cell.
* `exists_of_isOuterCellDart`: an outer cell dart of the doubled diagram is an old one other
  than `w_j`.
* `exists_cellFree`: induction on the number of outer cell darts.
* `outerCellThickening`: `OuterCellThickeningStatement`, from any distinguished section family
  over a boundary of length at least two.
* `spur_of_noOuterSpur`, `cell_outer_of_noOuterCellDart`: the two edge conditions.
* `leastArea_of_oEquivalent`: least area passes to O-equivalent diagrams.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OuterCellThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Basics

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- An **outer cell dart**: a dart on the exterior whose reverse lies on a relator cell. -/
def IsOuterCellDart (Delta : DiscDiagram.{u, w, v} W) (x : Delta.toCombMap.Dart) : Prop :=
  Delta.toCombMap.faceOf x = Delta.outerFace ∧
    ∃ C ∈ Delta.relatorCells, C.face = Delta.toCombMap.faceOf (Delta.toCombMap.alpha x)

/-- The number of outer cell darts. -/
noncomputable def outerCellCount (Delta : DiscDiagram.{u, w, v} W) : ℕ :=
  (Finset.univ.filter (IsOuterCellDart Delta)).card

/-- A boundary word of length at least two gives an exterior traversal of length at least two. -/
theorem one_lt_outer_length {Delta : DiscDiagram.{u, w, v} W}
    (h : 1 < Delta.boundaryWord.length) :
    1 < (Delta.faceBoundary Delta.outerFace).darts.length := by
  have hw : (Delta.faceWord Delta.outerFace).length =
      (Delta.faceBoundary Delta.outerFace).darts.length := by
    rw [DiscDiagram.faceWord, List.length_map]
  rw [Delta.boundaryWord_length, ← Delta.faceWord_length, hw] at h
  exact h

/-- No relator word of value one passes to O-equivalent diagrams. -/
theorem relatorValue_ne_one_of_oEquivalent {Delta Xi : DiscDiagram.{u, w, v} W}
    (E : OEquivalentDiscDiagram Delta Xi)
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1) :
    ∀ C ∈ Xi.relatorCells, RelLetter.listVal C.word ≠ 1 := by
  intro C hC
  obtain ⟨k, rfl⟩ := List.get_of_mem hC
  have hk := E.cellWord_eq (E.cellIndex.symm k)
  rw [Equiv.apply_symm_apply] at hk
  change RelLetter.listVal (Embedded.cell Xi k).word ≠ 1
  rw [hk]
  exact hvalue _ (Embedded.cell_mem Delta _)

/-- **Least area passes to O-equivalent diagrams**: they have the same boundary value and the
same number of relator cells. -/
theorem leastArea_of_oEquivalent {Delta Xi : DiscDiagram.{u, w, v} W}
    (E : OEquivalentDiscDiagram Delta Xi) (h : Delta.LeastArea) : Xi.LeastArea := by
  unfold DiscDiagram.LeastArea at h ⊢
  intro m hm
  have hval : Xi.boundaryValue = Delta.boundaryValue :=
    congrArg RelLetter.listVal E.boundaryWord_eq
  rw [hval] at hm
  have hcount : Xi.rCellCount = Delta.rCellCount := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr E.cellIndex).symm
  rw [hcount]
  exact h hm

/-- Without outer spurs, no edge has the exterior on both sides (`CopyClean.spur`). -/
theorem spur_of_noOuterSpur {Delta : DiscDiagram.{u, w, v} W}
    (hno : ∀ x, ¬ OuterSpurThickening.IsOuterSpur Delta x) :
    ∀ d, Delta.toCombMap.faceOf d = Delta.outerFace →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠ Delta.outerFace :=
  fun d h1 h2 => hno d ⟨h1, h2⟩

/-- Without outer cell darts, no edge joins a relator cell to the exterior
(`CopyClean.cell_outer`, for every source cell). -/
theorem cell_outer_of_noOuterCellDart {Delta : DiscDiagram.{u, w, v} W}
    (hno : ∀ x, ¬ IsOuterCellDart Delta x) (i : Fin Delta.rCellCount) :
    ∀ d, Delta.toCombMap.faceOf d = (Embedded.cell Delta i).face →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠ Delta.outerFace := by
  intro d hd hout
  apply hno (Delta.toCombMap.alpha d)
  refine ⟨hout, Embedded.cell Delta i, Embedded.cell_mem Delta i, ?_⟩
  rw [Delta.toCombMap.alpha_involutive d, hd]

end Basics

section Thickening

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W)
  (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
  (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)

/-- The first new dart lies on the digon. -/
theorem faceOf_none :
    (OuterSpurThickening.diagram Delta j hlen).toCombMap.faceOf none =
      FaceEdgeDoubling.digon Delta Delta.outerFace j hlen := by
  apply ((FaceEdgeDoubling.boundary Delta Delta.outerFace j hlen
    (FaceEdgeDoubling.digon Delta Delta.outerFace j hlen)).mem_iff _).mp
  rw [FaceEdgeDoubling.boundary_digon]
  exact List.mem_cons.mpr (Or.inl rfl)

/-- The doubled dart lies on the digon. -/
theorem faceOf_embed_dart :
    (OuterSpurThickening.diagram Delta j hlen).toCombMap.faceOf
        (embed Delta.toCombMap (FaceEdgeDoubling.dart Delta Delta.outerFace j)) =
      FaceEdgeDoubling.digon Delta Delta.outerFace j hlen := by
  apply ((FaceEdgeDoubling.boundary Delta Delta.outerFace j hlen
    (FaceEdgeDoubling.digon Delta Delta.outerFace j hlen)).mem_iff _).mp
  rw [FaceEdgeDoubling.boundary_digon]
  exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- Every old dart other than the doubled one keeps its face. -/
theorem faceOf_embed {y : Delta.toCombMap.Dart}
    (hy : y ≠ FaceEdgeDoubling.dart Delta Delta.outerFace j) :
    (OuterSpurThickening.diagram Delta j hlen).toCombMap.faceOf (embed Delta.toCombMap y) =
      FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen (Delta.toCombMap.faceOf y) := by
  by_cases hg : Delta.toCombMap.faceOf y = Delta.outerFace
  · rw [hg, FaceEdgeDoubling.faceImage_self]
    apply ((FaceEdgeDoubling.boundary Delta Delta.outerFace j hlen
      (FaceEdgeDoubling.cellFace Delta Delta.outerFace j hlen)).mem_iff _).mp
    rw [FaceEdgeDoubling.boundary_cellFace_darts]
    refine List.mem_map.mpr ⟨y, ((Delta.faceBoundary Delta.outerFace).mem_iff y).mpr hg, ?_⟩
    rw [FaceEdgeDoubling.dartImage, if_neg hy]
  · rw [FaceEdgeDoubling.faceImage_of_ne Delta Delta.outerFace j hlen hg]
    apply ((FaceEdgeDoubling.boundary Delta Delta.outerFace j hlen
      (FaceEdgeDoubling.keep Delta Delta.outerFace j hlen
        (Delta.toCombMap.faceOf y))).mem_iff _).mp
    rw [FaceEdgeDoubling.boundary_kept Delta Delta.outerFace j hlen hg]
    exact List.mem_map.mpr ⟨y, ((Delta.faceBoundary _).mem_iff y).mpr rfl, rfl⟩

/-- **An outer cell dart of the doubled diagram is an old outer cell dart other than `w_j`.**
The new exterior dart has its reverse on the digon, and the digon is no relator cell. -/
theorem exists_of_isOuterCellDart
    {x : (OuterSpurThickening.diagram Delta j hlen).toCombMap.Dart}
    (hx : IsOuterCellDart (OuterSpurThickening.diagram Delta j hlen) x) :
    ∃ d, embed Delta.toCombMap d = x ∧ IsOuterCellDart Delta d ∧
      d ≠ FaceEdgeDoubling.dart Delta Delta.outerFace j := by
  obtain ⟨d, hd, hdx⟩ := (OuterSpurThickening.faceOf_eq_outer_iff Delta j hlen x).mp hx.1
  obtain ⟨C, hC, hCf⟩ := hx.2
  have hC' : C ∈ Delta.relatorCells.map (OuterSpurThickening.spurCell Delta j hlen) := hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC'
  by_cases hdd : d = FaceEdgeDoubling.dart Delta Delta.outerFace j
  · rw [FaceEdgeDoubling.dartImage, if_pos hdd] at hdx
    subst hdx
    change FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen C₀.face =
      (OuterSpurThickening.diagram Delta j hlen).toCombMap.faceOf none at hCf
    rw [faceOf_none] at hCf
    exact (FaceEdgeDoubling.faceImage_ne_digon Delta Delta.outerFace j hlen C₀.face hCf).elim
  · rw [FaceEdgeDoubling.dartImage, if_neg hdd] at hdx
    subst hdx
    change FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen C₀.face =
      (OuterSpurThickening.diagram Delta j hlen).toCombMap.faceOf
        (embed Delta.toCombMap (Delta.toCombMap.alpha d)) at hCf
    by_cases had : Delta.toCombMap.alpha d = FaceEdgeDoubling.dart Delta Delta.outerFace j
    · rw [had, faceOf_embed_dart Delta j hlen] at hCf
      exact (FaceEdgeDoubling.faceImage_ne_digon Delta Delta.outerFace j hlen C₀.face hCf).elim
    · rw [faceOf_embed Delta j hlen had] at hCf
      exact ⟨d, rfl, ⟨hd, C₀, hC₀,
        FaceEdgeDoubling.faceImage_injective Delta Delta.outerFace j hlen hCf⟩, hdd⟩

/-- **Thickening an outer cell dart removes it and creates none.** -/
theorem outerCellCount_lt
    (hcell : IsOuterCellDart Delta (FaceEdgeDoubling.dart Delta Delta.outerFace j)) :
    outerCellCount (OuterSpurThickening.diagram Delta j hlen) < outerCellCount Delta := by
  have hmem : FaceEdgeDoubling.dart Delta Delta.outerFace j ∈
      Finset.univ.filter (IsOuterCellDart Delta) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩
  unfold outerCellCount
  refine lt_of_le_of_lt ?_ (Finset.card_erase_lt_of_mem hmem)
  refine Finset.card_le_card_of_injOn
    (fun x : (OuterSpurThickening.diagram Delta j hlen).toCombMap.Dart =>
      (Option.bind x id).getD (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ?_ ?_
  · intro x hx
    obtain ⟨d, rfl, hd, hne⟩ :=
      exists_of_isOuterCellDart Delta j hlen (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    exact Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩)
  · intro x hx y hy hxy
    obtain ⟨d, rfl, -, -⟩ :=
      exists_of_isOuterCellDart Delta j hlen (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    obtain ⟨e, rfl, -, -⟩ :=
      exists_of_isOuterCellDart Delta j hlen (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    exact congrArg (embed Delta.toCombMap) hxy

/-- An outer doubling creates no outer spur. -/
theorem noOuterSpur (hfree : ∀ x, ¬ OuterSpurThickening.IsOuterSpur Delta x) :
    ∀ x, ¬ OuterSpurThickening.IsOuterSpur (OuterSpurThickening.diagram Delta j hlen) x := by
  intro x hx
  obtain ⟨d, -, hd, -⟩ := OuterSpurThickening.exists_of_isOuterSpur Delta j hlen hx
  exact hfree d hd

/-- The relator words are unchanged. -/
theorem relatorValue_ne_one
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1) :
    ∀ C ∈ (OuterSpurThickening.diagram Delta j hlen).relatorCells,
      RelLetter.listVal C.word ≠ 1 := by
  intro C hC
  have hC' : C ∈ Delta.relatorCells.map (OuterSpurThickening.spurCell Delta j hlen) := hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC'
  exact hvalue C₀ hC₀

/-- When no relator word has value one, no region contains the relator cell across an outer
cell dart. -/
theorem cell_avoid {D : RelGenSet G Lambda} {eps : ℕ}
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hcell : IsOuterCellDart Delta (FaceEdgeDoubling.dart Delta Delta.outerFace j))
    (family : Finset (RegionCandidate D eps Delta)) :
    ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1 := by
  intro a _ hmem
  obtain ⟨C, hC, hCf⟩ := hcell.2
  have hone := (a.2.boundary.all_gCells _ hmem).2
  rw [← hCf] at hone
  apply hvalue C hC
  rw [Delta.relatorCell_word C hC]
  exact hone

end Thickening

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A distinguished section family across the thickening of an exterior dart** whose
reverse lies on a face no region contains.  The weight and the number of regions are unchanged
and the labels stay legal, so the transported family is again optimal. -/
noncomputable def sectionFamilyOfAvoid
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
      (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) ∉ a.1) :
    GloballyDistinguishedSectionFamily D lambda c eps Delta cuts where
  diagram := OuterSpurThickening.diagram S.diagram j hlen
  equiv := S.equiv.trans (OuterSpurThickening.oEquivalent S.diagram j hlen)
  reduced := OuterSpurThickening.reduced S.diagram j hlen S.reduced
  family := OuterSpurThickening.regionFamily S.diagram j hlen S.family havoid
  pairwise :=
    OuterSpurThickening.regionFamily_pairwise S.diagram j hlen S.family havoid S.pairwise
  respects := by
    intro a ha
    obtain ⟨b, hb, hab⟩ :=
      OuterSpurThickening.regionFamily_profile S.diagram j hlen S.family havoid ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab
      (OuterSpurThickening.regionFamily_noLoop S.diagram j hlen S.family havoid
        (fun x hx => (S.respects x hx).1) ha)
      (S.respects b hb)
  nondegenerate := by
    intro a ha
    obtain ⟨b, hb, hab⟩ :=
      OuterSpurThickening.regionFamily_profile S.diagram j hlen S.family havoid ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b hb
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩
  label_admissible :=
    OuterSpurThickening.label_admissible S.diagram j hlen (symmetricLabelAlphabet D)
      (symmetricLabelAlphabet.symmetric D) S.label_admissible
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (OuterSpurThickening.regionFamily_weight S.diagram j hlen S.family havoid).symm
  card_minimal other hother hweight :=
    (OuterSpurThickening.regionFamily_card S.diagram j hlen S.family havoid).trans_le
      (S.card_minimal other hother (hweight.trans
        (OuterSpurThickening.regionFamily_weight S.diagram j hlen S.family havoid)))

/-- **Induction on the number of outer cell darts**, keeping the absence of outer spurs and of
relator words of value one. -/
theorem exists_cellFree (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hlen0 : 1 < Delta.boundaryWord.length)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hfree : ∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
          (∀ x, ¬ IsOuterCellDart S'.diagram x) ∧
            (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
              S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                  (e a).1.2.source.val = a.1.2.source.val := by
  revert hvalue hfree
  generalize hn : outerCellCount S.diagram = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hvalue hfree
    by_cases hcell : ∃ x, IsOuterCellDart S.diagram x
    · obtain ⟨x, hx⟩ := hcell
      have hbw : S.diagram.boundaryWord = Delta.boundaryWord := S.equiv.boundaryWord_eq
      have hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length :=
        one_lt_outer_length (by rw [hbw]; exact hlen0)
      obtain ⟨j, hj⟩ := List.get_of_mem
        (((S.diagram.faceBoundary S.diagram.outerFace).mem_iff x).mpr hx.1)
      have hcell2 :
          IsOuterCellDart S.diagram (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) := by
        rw [FaceEdgeDoubling.dart_eq_get, hj]
        exact hx
      have havoid := cell_avoid S.diagram j hvalue hcell2 S.family
      obtain ⟨S', e, ⟨equiv'⟩, hspur', hcell', hvalue', hweight, hprofile⟩ :=
        ih _ (lt_of_lt_of_eq (outerCellCount_lt S.diagram j hlen hcell2) hn)
          (sectionFamilyOfAvoid S j hlen havoid) rfl
          (relatorValue_ne_one S.diagram j hlen hvalue)
          (noOuterSpur S.diagram j hlen hfree)
      refine ⟨S', (OuterSpurThickening.regionFamilyEquiv S.diagram j hlen S.family havoid).trans e,
        ⟨(OuterSpurThickening.oEquivalent S.diagram j hlen).trans equiv'⟩, hspur', hcell',
        hvalue',
        hweight.trans (OuterSpurThickening.regionFamily_weight S.diagram j hlen S.family havoid),
        fun a => ?_⟩
      obtain ⟨hprof, hsource⟩ :=
        hprofile (OuterSpurThickening.regionFamilyEquiv S.diagram j hlen S.family havoid a)
      exact And.intro
        (hprof.trans
          (OuterSpurThickening.regionFamilyEquiv_profile S.diagram j hlen S.family havoid a))
        (hsource.trans
          (OuterSpurThickening.regionFamilyEquiv_source S.diagram j hlen S.family havoid a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, hfree,
        fun x hx => hcell ⟨x, hx⟩, hvalue, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl⟩

end Family

/-- **Outer cell thickening.**  A distinguished section family over a boundary word of length at
least two, with no relator word of value one, has a distinguished section family over the same
cuts whose diagram is O-equivalent to the old one, has no outer spur, and has no edge between a
relator cell and the exterior.  No relator word of the new diagram has value one.  Its regions
correspond bijectively to the old ones, with the same total weight, and every region keeps its
target profile and the index of its source cell. -/
def OuterCellThickeningStatement : Prop :=
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
              (∀ x, ¬ IsOuterCellDart S'.diagram x) ∧
                (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                  S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                    ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                      (e a).1.2.source.val = a.1.2.source.val

theorem outerCellThickening : OuterCellThickeningStatement.{u, w, v} := by
  unfold OuterCellThickeningStatement
  intro _ _ _ D lambda c eps W Delta cuts S hlen0 hvalue
  obtain ⟨S₁, e₁, ⟨equiv₁⟩, hfree₁, hweight₁, hprofile₁⟩ :=
    OuterSpurThickening.outerSpurThickening D lambda c eps W Delta cuts S
  obtain ⟨S₂, e₂, ⟨equiv₂⟩, hfree₂, hcell₂, hvalue₂, hweight₂, hprofile₂⟩ :=
    exists_cellFree S₁ hlen0 (relatorValue_ne_one_of_oEquivalent equiv₁ hvalue) hfree₁
  refine ⟨S₂, e₁.trans e₂, ⟨equiv₁.trans equiv₂⟩, hfree₂, hcell₂, hvalue₂,
    hweight₂.trans hweight₁, fun a => ?_⟩
  obtain ⟨hprof₂, hsource₂⟩ := hprofile₂ (e₁ a)
  obtain ⟨hprof₁, hsource₁⟩ := hprofile₁ a
  exact And.intro (hprof₂.trans hprof₁) (hsource₂.trans hsource₁)

end GroupApproximation.GGT.VanKampen.OuterCellThickening

#audit_closed_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.outerCellThickening
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.one_lt_outer_length
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.relatorValue_ne_one_of_oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.leastArea_of_oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.spur_of_noOuterSpur
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.cell_outer_of_noOuterCellDart
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.exists_of_isOuterCellDart
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.outerCellCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.sectionFamilyOfAvoid
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.exists_cellFree
