import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingSideRegions
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOne
import GroupApproximation.Meta.AxiomGuard

/-!
# Thickening relator-face edges across region sides

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1, s_2` are side arcs of contiguity subdiagrams of the
cell `Π`.

The pocket walk of two exterior regions `x`, `y` of `Π` has no repeated dart only if no side
dart of `y` or `x` has `Π` across it (the field `side_cell` of `PocketWalk.CopyClean`,
`Estimating/OsinPocketCopyWalk.lean`).  On an optimal diagram a side arc can come back to a
relator face after leaving it.  Doubling that edge inside the relator face
(`FaceEdgeDoubling.diagram`) puts a G-cell digon between the relator face and the side.
Every old dart, face set and label survives.

* `IsCellSideDart`: a dart of a relator face with at least two darts, lying in no region of
  the family, whose reverse is a left or right side dart of a region of the family.
* `cellSideCount`: the number of cell-side darts.
* `CellSideThickeningStatement`: a distinguished section family has one over the same cuts,
  on an O-equivalent diagram, with no cell-side dart.  Its regions correspond to the old
  ones, with the same weight, target profiles and source indices.  The output shape is that
  of `OuterSpurThickening.OuterSpurThickeningStatement`.

The proof doubles one cell-side dart at a time.
* The doubled dart lies in neither contiguity arc of any region (`familyArcAvoid_of_side`), so
  the family transports (`FaceEdgeDoubling.regionFamilyOfArcs`) and stays optimal
  (`sectionFamilyOfArcs`).
* A cell-side dart of the new diagram is the image of an old cell-side dart other than the
  doubled one (`exists_of_isCellSideDart`).  The doubled dart itself lies in the digon, which
  is not a relator face.  So the count drops (`cellSideCount_lt`).
* Induction on the count gives `cellSideThickening`.

A relator face with one dart is left out, because `FaceEdgeDoubling` needs two darts.  At the
source cell of a nondegenerate exterior region, that one dart lies in the source arc.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellSideThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Darts

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- A **cell-side dart** of a family of regions: a dart of a relator face with at least two
darts, lying in no region of the family, whose reverse is a left or right side dart of a region
of the family. -/
def IsCellSideDart (Delta : DiscDiagram.{u, w, v} W)
    (family : Finset (RegionCandidate D eps Delta)) (x : Delta.toCombMap.Dart) : Prop :=
  (∃ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf x = C.face) ∧
    1 < (Delta.faceBoundary (Delta.toCombMap.faceOf x)).darts.length ∧
      (∀ a ∈ family, Delta.toCombMap.faceOf x ∉ a.1) ∧
        ∃ a ∈ family, Delta.toCombMap.alpha x ∈ a.2.rightSide ++ a.2.leftSide

/-- The number of cell-side darts. -/
noncomputable def cellSideCount (Delta : DiscDiagram.{u, w, v} W)
    (family : Finset (RegionCandidate D eps Delta)) : ℕ :=
  (Finset.univ.filter (IsCellSideDart Delta family)).card

/-- No cell-side dart exactly when the count is zero. -/
theorem cellSideCount_eq_zero_iff (Delta : DiscDiagram.{u, w, v} W)
    (family : Finset (RegionCandidate D eps Delta)) :
    cellSideCount Delta family = 0 ↔ ∀ x, ¬ IsCellSideDart Delta family x := by
  unfold cellSideCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x
    exact h (Finset.mem_univ x)
  · intro h x _
    exact h x

end Darts

/-- **Cell-side thickening.**  A distinguished section family has a distinguished section
family over the same cuts whose diagram is O-equivalent to the old one and has no cell-side
dart.  Its regions correspond bijectively to the old ones, with the same total weight, and
every region keeps its target profile and the index of its source cell. -/
def CellSideThickeningStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsCellSideDart S'.diagram S'.family x) ∧
          S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
            ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
              (e a).1.2.source.val = a.1.2.source.val

section Doubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}
  (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- Every old dart other than `w_j` lies in the image of its face. -/
theorem faceOf_embed_of_ne_dart {e : Delta.toCombMap.Dart}
    (he : e ≠ FaceEdgeDoubling.dart Delta f j) :
    (FaceEdgeDoubling.map Delta f j hlen).faceOf (EdgeInsertion.embed Delta.toCombMap e) =
      FaceEdgeDoubling.faceImage Delta f j hlen (Delta.toCombMap.faceOf e) := by
  by_cases hef : Delta.toCombMap.faceOf e = f
  · rw [FaceEdgeDoubling.faceOf_embed_of_face_of_ne Delta f j hlen hef he, hef,
      FaceEdgeDoubling.faceImage_self]
  · exact FaceEdgeDoubling.faceOf_embed_of_face_ne Delta f j hlen hef

/-- **A cell-side dart after the doubling is the image of an old cell-side dart other than
`w_j`.**  Its reverse is the image of a side dart of an old region, so it is the image of an old
dart.  That dart is not `w_j`, whose image lies in the digon; its face is a relator face with as
many darts as before and in no old region. -/
theorem exists_of_isCellSideDart (family : Finset (RegionCandidate D eps Delta))
    (havoid : FaceEdgeDoubling.FamilyArcAvoid Delta f j family)
    {x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hx : IsCellSideDart (FaceEdgeDoubling.diagram Delta f j hlen hf)
      (FaceEdgeDoubling.regionFamilyOfArcs Delta f j hlen hf family havoid) x) :
    ∃ e, EdgeInsertion.embed Delta.toCombMap e = x ∧ IsCellSideDart Delta family e ∧
      e ≠ FaceEdgeDoubling.dart Delta f j := by
  obtain ⟨⟨C', hC', hxC'⟩, hlenx, hnotx, a', ha', hsidex⟩ := hx
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp ha'
  have hmap : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha x ∈
      (b.val.2.rightSide ++ b.val.2.leftSide).map
        (FaceEdgeDoubling.embedding Delta f j hlen hf).darts := by
    rw [List.map_append]
    exact hsidex
  obtain ⟨d, hd, hdx⟩ := List.mem_map.mp hmap
  have hxe : EdgeInsertion.embed Delta.toCombMap (Delta.toCombMap.alpha d) = x := by
    have h := congrArg (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha hdx
    rw [(FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha_involutive x,
      (FaceEdgeDoubling.embedding Delta f j hlen hf).alpha d] at h
    exact h
  have hC'' : C' ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC'
  have hne : Delta.toCombMap.alpha d ≠ FaceEdgeDoubling.dart Delta f j := by
    intro hed
    have hdig : (FaceEdgeDoubling.map Delta f j hlen).faceOf x =
        FaceEdgeDoubling.digon Delta f j hlen := by
      rw [← hxe, hed]
      exact FaceEdgeDoubling.faceOf_embed_dart_digon Delta f j hlen
    obtain ⟨C, -, rfl⟩ := List.mem_map.mp hC''
    exact FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen C.face (hxC'.symm.trans hdig)
  have hface : (FaceEdgeDoubling.map Delta f j hlen).faceOf x =
      FaceEdgeDoubling.faceImage Delta f j hlen
        (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d)) := by
    rw [← hxe]
    exact faceOf_embed_of_ne_dart Delta f j hlen hne
  refine ⟨Delta.toCombMap.alpha d, hxe, ⟨?_, ?_, ?_, b.val, b.property, ?_⟩, hne⟩
  · obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC''
    exact ⟨C, hC, FaceEdgeDoubling.faceImage_injective Delta f j hlen (hface.symm.trans hxC')⟩
  · have h : 1 < ((FaceEdgeDoubling.diagram Delta f j hlen hf).faceBoundary
        (FaceEdgeDoubling.faceImage Delta f j hlen
          (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d)))).darts.length := by
      rw [← hface]
      exact hlenx
    rwa [FaceEdgeDoubling.boundary_faceImage_darts, List.length_map] at h
  · intro b' hb' hin
    apply hnotx _ (Finset.mem_map_of_mem _ (Finset.mem_attach family ⟨b', hb'⟩))
    show (FaceEdgeDoubling.map Delta f j hlen).faceOf x ∈
      (FaceEdgeDoubling.embedding Delta f j hlen hf).faceSet b'.1
    rw [hface]
    by_cases hef : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = f
    · exact absurd (hef ▸ hin) (havoid b' hb').1
    · rw [FaceEdgeDoubling.faceImage_of_ne Delta f j hlen hef]
      exact Finset.mem_map_of_mem _ hin
  · rw [Delta.toCombMap.alpha_involutive d]
    exact hd

/-- **Doubling a cell-side dart removes it and creates none.** -/
theorem cellSideCount_lt (family : Finset (RegionCandidate D eps Delta))
    (havoid : FaceEdgeDoubling.FamilyArcAvoid Delta f j family)
    (hw : IsCellSideDart Delta family (FaceEdgeDoubling.dart Delta f j)) :
    cellSideCount (FaceEdgeDoubling.diagram Delta f j hlen hf)
        (FaceEdgeDoubling.regionFamilyOfArcs Delta f j hlen hf family havoid) <
      cellSideCount Delta family := by
  have hmem : FaceEdgeDoubling.dart Delta f j ∈
      Finset.univ.filter (IsCellSideDart Delta family) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
  unfold cellSideCount
  refine lt_of_le_of_lt ?_ (Finset.card_erase_lt_of_mem hmem)
  refine Finset.card_le_card_of_injOn
    (fun x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart =>
      (Option.bind x id).getD (FaceEdgeDoubling.dart Delta f j)) ?_ ?_
  · intro x hx
    obtain ⟨e, rfl, he, hne⟩ := exists_of_isCellSideDart Delta f j hlen hf family havoid
      (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    exact Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩)
  · intro x hx y hy hxy
    obtain ⟨d, rfl, -, -⟩ := exists_of_isCellSideDart Delta f j hlen hf family havoid
      (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    obtain ⟨e, rfl, -, -⟩ := exists_of_isCellSideDart Delta f j hlen hf family havoid
      (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    exact congrArg (EdgeInsertion.embed Delta.toCombMap) hxy

end Doubling

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A distinguished section family across the doubling of a relator-face edge**, when the
doubled dart lies in no arc of the family.  The weight and the number of regions are unchanged
and the labels stay legal, so the transported family is again optimal. -/
noncomputable def sectionFamilyOfArcs
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family) :
    GloballyDistinguishedSectionFamily D lambda c eps Delta cuts where
  diagram := FaceEdgeDoubling.diagram S.diagram f j hlen hf
  equiv := S.equiv.trans (FaceEdgeDoubling.oEquivalent S.diagram f j hlen hf)
  reduced := FaceEdgeDoubling.reduced S.diagram f j hlen hf S.reduced
  family := FaceEdgeDoubling.regionFamilyOfArcs S.diagram f j hlen hf S.family havoid
  pairwise := FaceEdgeDoubling.regionFamilyOfArcs_pairwise S.diagram f j hlen hf S.family havoid
    S.pairwise
  respects := by
    intro a ha
    obtain ⟨b, hb, hab⟩ :=
      FaceEdgeDoubling.regionFamilyOfArcs_profile S.diagram f j hlen hf S.family havoid ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab
      (FaceEdgeDoubling.regionFamilyOfArcs_noLoop S.diagram f j hlen hf S.family havoid
        (fun x hx => (S.respects x hx).1) ha)
      (S.respects b hb)
  nondegenerate := by
    intro a ha
    obtain ⟨b, hb, hab⟩ :=
      FaceEdgeDoubling.regionFamilyOfArcs_profile S.diagram f j hlen hf S.family havoid ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b hb
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩
  label_admissible := FaceEdgeDoubling.label_admissible S.diagram f j hlen hf
    (symmetricLabelAlphabet D) (symmetricLabelAlphabet.symmetric D) S.label_admissible
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (FaceEdgeDoubling.regionFamilyOfArcs_weight S.diagram f j hlen hf S.family havoid).symm
  card_minimal other hother hweight :=
    (FaceEdgeDoubling.regionFamilyOfArcs_card S.diagram f j hlen hf S.family havoid).trans_le
      (S.card_minimal other hother (hweight.trans
        (FaceEdgeDoubling.regionFamilyOfArcs_weight S.diagram f j hlen hf S.family havoid)))

/-- **Induction on the number of cell-side darts, carrying an invariant.**  Every property of
distinguished section families that one doubling step `sectionFamilyOfArcs` preserves also
holds for the output. -/
theorem exists_cellSideFree_of_invariant
    (P : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts → Prop)
    (hP : ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
      (havoid : FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family),
      P S → P (sectionFamilyOfArcs S f j hlen hf havoid))
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) (hS : P S) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsCellSideDart S'.diagram S'.family x) ∧
          S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
            (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
              (e a).1.2.source.val = a.1.2.source.val) ∧ P S' := by
  generalize hn : cellSideCount S.diagram S.family = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hdart : ∃ x, IsCellSideDart S.diagram S.family x
    · obtain ⟨x, hx⟩ := hdart
      obtain ⟨⟨C, hC, hxC⟩, hlen, hnot, z, hz, hside⟩ := hx
      have hf : S.diagram.toCombMap.faceOf x ≠ S.diagram.outerFace := by
        rw [hxC]
        exact C.face_ne_outer
      obtain ⟨j, hj⟩ := List.get_of_mem
        (((S.diagram.faceBoundary (S.diagram.toCombMap.faceOf x)).mem_iff x).mpr rfl)
      have hdartx : FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j = x := by
        rw [FaceEdgeDoubling.dart_eq_get, hj]
      have hside' : S.diagram.toCombMap.alpha
          (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j) ∈
            z.2.rightSide ++ z.2.leftSide := by
        rw [hdartx]
        exact hside
      have havoid := FaceEdgeDoubling.familyArcAvoid_of_side S.diagram
        (S.diagram.toCombMap.faceOf x) j S.family S.pairwise hnot hz hside'
      have hw : IsCellSideDart S.diagram S.family
          (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j) := by
        rw [hdartx]
        exact ⟨⟨C, hC, hxC⟩, hlen, hnot, z, hz, hside⟩
      obtain ⟨S', e, ⟨equiv'⟩, hfree, hweight, hprofile, hPS'⟩ :=
        ih _ (lt_of_lt_of_eq
          (cellSideCount_lt S.diagram _ j hlen hf S.family havoid hw) hn)
          (sectionFamilyOfArcs S _ j hlen hf havoid) (hP S _ j hlen hf havoid hS) rfl
      refine ⟨S', (FaceEdgeDoubling.regionFamilyOfArcsEquiv S.diagram _ j hlen hf S.family
          havoid).trans e,
        ⟨(FaceEdgeDoubling.oEquivalent S.diagram _ j hlen hf).trans equiv'⟩, hfree,
        hweight.trans
          (FaceEdgeDoubling.regionFamilyOfArcs_weight S.diagram _ j hlen hf S.family havoid),
        fun a => ?_, hPS'⟩
      obtain ⟨hprof, hsource⟩ := hprofile
        (FaceEdgeDoubling.regionFamilyOfArcsEquiv S.diagram _ j hlen hf S.family havoid a)
      exact And.intro
        (hprof.trans (FaceEdgeDoubling.regionFamilyOfArcsEquiv_profile S.diagram _ j hlen hf
          S.family havoid a))
        (hsource.trans (FaceEdgeDoubling.regionFamilyOfArcsEquiv_source S.diagram _ j hlen hf
          S.family havoid a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, fun x hx => hdart ⟨x, hx⟩, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl, hS⟩

/-- **Induction on the number of cell-side darts.** -/
theorem exists_cellSideFree (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsCellSideDart S'.diagram S'.family x) ∧
          S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
            ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
              (e a).1.2.source.val = a.1.2.source.val := by
  obtain ⟨S', e, hequiv, hfree, hweight, hprofile, -⟩ :=
    exists_cellSideFree_of_invariant (fun _ => True) (fun _ _ _ _ _ _ _ => trivial) S trivial
  exact ⟨S', e, hequiv, hfree, hweight, hprofile⟩

end Family

/-- **Cell-side thickening, proved.** -/
theorem cellSideThickening : CellSideThickeningStatement.{u, w, v} := by
  unfold CellSideThickeningStatement
  intro _ _ _ _ _ _ _ _ _ _ S
  exact exists_cellSideFree S

end GroupApproximation.GGT.VanKampen.CellSideThickening

#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.cellSideThickening
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.cellSideCount_eq_zero_iff
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.exists_of_isCellSideDart
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.cellSideCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.sectionFamilyOfArcs
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.exists_cellSideFree_of_invariant
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.exists_cellSideFree
