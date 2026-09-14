import GroupApproximation.GGT.VanKampen.SurgeryOuterSideThickening
import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# The outer and cell hair thickenings, keeping an invariant

`CellEdgeThickening.exists_cellEdgeFree_of_invariant`, `CellSideThickening.exists_cellSideFree_of_invariant`
and `RegionPairThickening.exists_regionPairFree_of_invariant` carry a property of the family through
every doubling step.  The outer spur, outer cell, outer side and cell hair thickenings have no such
form.  This module gives it, with the same strong induction on the number of offending darts as
`exists_spurFree`, `exists_cellFree`, `exists_sideFree` and `exists_cellHairFree`.

* `OuterSpurThickening.exists_spurFree_of_invariant`
* `OuterCellThickening.exists_cellFree_of_invariant`
* `OuterSideThickening.exists_sideFree_of_invariant`
* `CellHairThickening.exists_cellHairFree_of_invariant`

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

universe u w v

namespace GroupApproximation.GGT.VanKampen.OuterSpurThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Outer spur thickening, keeping an invariant.** -/
theorem exists_spurFree_of_invariant
    (P : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts → Prop)
    (hP : ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (hspur : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) = S.diagram.outerFace),
      P S → P (sectionFamily S j hlen hspur))
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) (hS : P S) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsOuterSpur S'.diagram x) ∧
          S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
            (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
              (e a).1.2.source.val = a.1.2.source.val) ∧ P S' := by
  revert hS
  generalize hn : outerSpurCount S.diagram = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hS
    by_cases hspur : ∃ x, IsOuterSpur S.diagram x
    · obtain ⟨x, hx⟩ := hspur
      have hlen := one_lt_length_of_isOuterSpur S.diagram hx
      obtain ⟨j, hj⟩ := List.get_of_mem
        (((S.diagram.faceBoundary S.diagram.outerFace).mem_iff x).mpr hx.1)
      have hspur2 : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
          (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) = S.diagram.outerFace := by
        rw [FaceEdgeDoubling.dart_eq_get, hj]
        exact hx.2
      have havoid := spur_avoid S.diagram j hspur2 S.family
      obtain ⟨S', e, ⟨equiv'⟩, hfree, hweight, hprofile, hPS'⟩ :=
        ih _ (lt_of_lt_of_eq (outerSpurCount_lt S.diagram j hlen hspur2) hn)
          (sectionFamily S j hlen hspur2) rfl (hP S j hlen hspur2 hS)
      refine ⟨S', (regionFamilyEquiv S.diagram j hlen S.family havoid).trans e,
        ⟨(oEquivalent S.diagram j hlen).trans equiv'⟩, hfree,
        hweight.trans (regionFamily_weight S.diagram j hlen S.family havoid), fun a => ?_, hPS'⟩
      obtain ⟨hprof, hsource⟩ := hprofile (regionFamilyEquiv S.diagram j hlen S.family havoid a)
      exact And.intro (hprof.trans (regionFamilyEquiv_profile S.diagram j hlen S.family havoid a))
        (hsource.trans (regionFamilyEquiv_source S.diagram j hlen S.family havoid a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, fun x hx => hspur ⟨x, hx⟩, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl, hS⟩

end GroupApproximation.GGT.VanKampen.OuterSpurThickening

namespace GroupApproximation.GGT.VanKampen.OuterCellThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Outer cell thickening, keeping an invariant.** -/
theorem exists_cellFree_of_invariant
    (P : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts → Prop)
    (hP : ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) ∉ a.1),
      P S → P (sectionFamilyOfAvoid S j hlen havoid))
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hlen0 : 1 < Delta.boundaryWord.length)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hfree : ∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x) (hS : P S) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
          (∀ x, ¬ IsOuterCellDart S'.diagram x) ∧
            (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
              S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                  (e a).1.2.source.val = a.1.2.source.val) ∧ P S' := by
  revert hvalue hfree hS
  generalize hn : outerCellCount S.diagram = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hvalue hfree hS
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
      obtain ⟨S', e, ⟨equiv'⟩, hspur', hcell', hvalue', hweight, hprofile, hPS'⟩ :=
        ih _ (lt_of_lt_of_eq (outerCellCount_lt S.diagram j hlen hcell2) hn)
          (sectionFamilyOfAvoid S j hlen havoid) rfl
          (relatorValue_ne_one S.diagram j hlen hvalue)
          (noOuterSpur S.diagram j hlen hfree) (hP S j hlen havoid hS)
      refine ⟨S', (OuterSpurThickening.regionFamilyEquiv S.diagram j hlen S.family havoid).trans e,
        ⟨(OuterSpurThickening.oEquivalent S.diagram j hlen).trans equiv'⟩, hspur', hcell',
        hvalue',
        hweight.trans (OuterSpurThickening.regionFamily_weight S.diagram j hlen S.family havoid),
        fun a => ?_, hPS'⟩
      obtain ⟨hprof, hsource⟩ :=
        hprofile (OuterSpurThickening.regionFamilyEquiv S.diagram j hlen S.family havoid a)
      exact And.intro
        (hprof.trans
          (OuterSpurThickening.regionFamilyEquiv_profile S.diagram j hlen S.family havoid a))
        (hsource.trans
          (OuterSpurThickening.regionFamilyEquiv_source S.diagram j hlen S.family havoid a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, hfree,
        fun x hx => hcell ⟨x, hx⟩, hvalue, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl, hS⟩

end GroupApproximation.GGT.VanKampen.OuterCellThickening

namespace GroupApproximation.GGT.VanKampen.OuterSideThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Outer side thickening, keeping an invariant.** -/
theorem exists_sideFree_of_invariant
    (P : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts → Prop)
    (hP : ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (htgt : ∀ a ∈ S.family, S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) ∉ a.2.targetArc.darts),
      P S → P (sectionFamilyOfTransport S j hlen htgt))
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hlen0 : 1 < Delta.boundaryWord.length)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hfree : ∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x)
    (hcell : ∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x) (hS : P S) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
          (∀ x, ¬ OuterCellThickening.IsOuterCellDart S'.diagram x) ∧
            (∀ x, ¬ IsOuterSideDart S'.diagram S'.family x) ∧
              (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                  (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                    (e a).1.2.source.val = a.1.2.source.val) ∧ P S' := by
  revert hvalue hfree hcell hS
  generalize hn : outerSideCount S.diagram S.family = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hvalue hfree hcell hS
    by_cases hside : ∃ x, IsOuterSideDart S.diagram S.family x
    · obtain ⟨x, hx⟩ := hside
      have hbw : S.diagram.boundaryWord = Delta.boundaryWord := S.equiv.boundaryWord_eq
      have hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length :=
        OuterCellThickening.one_lt_outer_length (by rw [hbw]; exact hlen0)
      obtain ⟨j, hj⟩ := List.get_of_mem
        (((S.diagram.faceBoundary S.diagram.outerFace).mem_iff x).mpr hx.1)
      have hside2 : IsOuterSideDart S.diagram S.family
          (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) := by
        rw [FaceEdgeDoubling.dart_eq_get, hj]
        exact hx
      have htgt := not_mem_targetArc_of_outerSide S.diagram j S.family S.pairwise hside2
      obtain ⟨S', e, ⟨equiv'⟩, hspur', hcell', hside', hvalue', hweight, hprofile, hPS'⟩ :=
        ih _ (lt_of_lt_of_eq (outerSideCount_lt S.diagram j hlen S.family htgt hside2) hn)
          (sectionFamilyOfTransport S j hlen htgt) rfl
          (OuterCellThickening.relatorValue_ne_one S.diagram j hlen hvalue)
          (OuterCellThickening.noOuterSpur S.diagram j hlen hfree)
          (noOuterCellDart S.diagram j hlen hcell) (hP S j hlen htgt hS)
      refine ⟨S', (OuterDoublingTransport.regionFamilyEquiv S.diagram j hlen S.family htgt).trans e,
        ⟨(OuterSpurThickening.oEquivalent S.diagram j hlen).trans equiv'⟩, hspur', hcell', hside',
        hvalue',
        hweight.trans (OuterDoublingTransport.regionFamily_weight S.diagram j hlen S.family htgt),
        fun a => ?_, hPS'⟩
      obtain ⟨hprof, hsource⟩ :=
        hprofile (OuterDoublingTransport.regionFamilyEquiv S.diagram j hlen S.family htgt a)
      exact And.intro
        (hprof.trans
          (OuterDoublingTransport.regionFamilyEquiv_profile S.diagram j hlen S.family htgt a))
        (hsource.trans
          (OuterDoublingTransport.regionFamilyEquiv_source S.diagram j hlen S.family htgt a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, hfree, hcell,
        fun x hx => hside ⟨x, hx⟩, hvalue, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl, hS⟩

end GroupApproximation.GGT.VanKampen.OuterSideThickening

namespace GroupApproximation.GGT.VanKampen.CellHairThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Cell hair thickening, keeping an invariant.** -/
theorem exists_cellHairFree_of_invariant
    (P : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts → Prop)
    (hP : ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
      (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1),
      P S → P (HairOpening.sectionFamily S f j hlen hf havoid))
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hspur : ∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x)
    (hcell : ∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x) (hS : P S) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
          (∀ x, ¬ OuterCellThickening.IsOuterCellDart S'.diagram x) ∧
            (∀ x, ¬ IsCellHair S'.diagram x) ∧
              (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                  (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                    (e a).1.2.source.val = a.1.2.source.val) ∧ P S' := by
  revert hvalue hspur hcell hS
  generalize hn : cellHairCount S.diagram = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hvalue hspur hcell hS
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
      obtain ⟨S', e, ⟨equiv'⟩, hspur', hcell', hhair', hvalue', hweight, hprofile, hPS'⟩ :=
        ih _ (lt_of_lt_of_eq (cellHairCount_lt S.diagram _ j hlen hf hcell2) hn)
          (HairOpening.sectionFamily S _ j hlen hf havoid) rfl
          (relatorValue_ne_one S.diagram _ j hlen hf hvalue)
          (noOuterSpur S.diagram _ j hlen hf hspur)
          (noOuterCellDart S.diagram _ j hlen hf hcell) (hP S _ j hlen hf havoid hS)
      refine ⟨S', (HairOpening.regionFamilyEquiv S.diagram _ j hlen hf S.family havoid).trans e,
        ⟨(FaceEdgeDoubling.oEquivalent S.diagram _ j hlen hf).trans equiv'⟩, hspur', hcell',
        hhair', hvalue',
        hweight.trans (FaceEdgeDoubling.regionFamily_weight S.diagram _ j hlen hf S.family havoid),
        fun a => ?_, hPS'⟩
      obtain ⟨hprof, hsource⟩ :=
        hprofile (HairOpening.regionFamilyEquiv S.diagram _ j hlen hf S.family havoid a)
      exact And.intro
        (hprof.trans
          (HairOpening.regionFamilyEquiv_profile S.diagram _ j hlen hf S.family havoid a))
        (hsource.trans
          (HairOpening.regionFamilyEquiv_source S.diagram _ j hlen hf S.family havoid a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, hspur, hcell,
        fun x hx => hhair ⟨x, hx⟩, hvalue, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl, hS⟩

end GroupApproximation.GGT.VanKampen.CellHairThickening

#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.exists_spurFree_of_invariant
#audit_axioms GroupApproximation.GGT.VanKampen.OuterCellThickening.exists_cellFree_of_invariant
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSideThickening.exists_sideFree_of_invariant
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.exists_cellHairFree_of_invariant
