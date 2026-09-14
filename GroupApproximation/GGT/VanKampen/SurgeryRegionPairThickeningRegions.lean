import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningCount
import GroupApproximation.GGT.VanKampen.SurgeryCellEdgeThickening
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFaceSetOnCopy
import GroupApproximation.Meta.AxiomGuard

/-!
# The region-pair thickening, proved

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Doubling a region-pair edge inside the face
of one region (`RegionPairThickening.sectionFamily`) removes that region-pair dart and creates none
(`regionPairCount_lt`).  Induction on the count gives a distinguished section family with no edge
from a face of one selected region to a face of another.

* `exists_of_mem_stepFamily_sides`: a side dart after the step is the image of an old side dart.
* `noOuterSideDart_step`, `noCellSideDart_step`, `noCellHair_step`, `noCellEdgeDart_step`: the step
  creates no outer-side dart, cell-side dart, cell hair or cell-edge dart.
* `exists_regionPairFree_of_invariant`: the induction, carrying an invariant, the absence of relator
  words of value one, and the source and target indices.
* `sectionPocketRegionsCopy`: `SectionPocketRegionsCopyStatement`, the `regions` stage of the clean
  copy (`Estimating/OsinPocketFaceSetOnCopy.lean`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.RegionPairThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Doubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}
  (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

variable {family : Finset (RegionCandidate D eps Delta)}

/-- **A side dart after the step is the image of an old side dart**: through the dart embedding,
or the new dart of `f` in the place of `w_j`. -/
theorem exists_of_mem_stepFamily_sides (T : StepData Delta f j family)
    {a' : RegionCandidate D eps (FaceEdgeDoubling.diagram Delta f j hlen hf)}
    (ha' : a' ∈ stepFamily Delta f j hlen hf T)
    {y : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hy : y ∈ a'.2.rightSide ++ a'.2.leftSide) :
    ∃ b ∈ family, ∃ d ∈ b.2.rightSide ++ b.2.leftSide,
      y = embed Delta.toCombMap d ∨
        y = FaceEdgeDoubling.dartImage Delta f j hlen (FaceEdgeDoubling.dart Delta f j) := by
  rcases Finset.mem_insert.mp ha' with rfl | ha''
  · have hmap : y ∈ (T.holder.2.rightSide ++ T.holder.2.leftSide).map
        (FaceEdgeDoubling.dartImage Delta f j hlen) := by
      rw [List.map_append]
      exact hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmap
    refine ⟨T.holder, T.holder_mem, d, hd, ?_⟩
    by_cases hdw : d = FaceEdgeDoubling.dart Delta f j
    · exact Or.inr (by rw [hdw])
    · exact Or.inl (FaceEdgeDoubling.Holding.dartImage_of_ne Delta f j hlen hdw)
  · obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp ha''
    have hmap : y ∈ (b.val.2.rightSide ++ b.val.2.leftSide).map
        (FaceEdgeDoubling.embedding Delta f j hlen hf).darts := by
      rw [List.map_append]
      exact hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmap
    exact ⟨b.val, Finset.mem_of_mem_erase b.property, d, hd, Or.inl rfl⟩

/-- **The step creates no outer-side dart.** -/
theorem noOuterSideDart_step (T : StepData Delta f j family)
    (hfree : ∀ x, ¬ OuterSideThickening.IsOuterSideDart Delta family x) :
    ∀ x, ¬ OuterSideThickening.IsOuterSideDart (FaceEdgeDoubling.diagram Delta f j hlen hf)
      (stepFamily Delta f j hlen hf T) x := by
  rintro x ⟨hx, a', ha', hside⟩
  obtain ⟨e, he, rfl⟩ := (CellSideThickening.faceOf_eq_outer_iff Delta f j hlen hf x).mp hx
  obtain ⟨b, hb, d, hd, hde | hde⟩ :=
    exists_of_mem_stepFamily_sides Delta f j hlen hf T ha' hside
  · have hde' : embed Delta.toCombMap (Delta.toCombMap.alpha e) = embed Delta.toCombMap d := hde
    have hda : Delta.toCombMap.alpha e = d := EdgeInsertion.embed_injective Delta.toCombMap hde'
    exact hfree e ⟨he, b, hb, hda ▸ hd⟩
  · rw [FaceEdgeDoubling.Holding.dartImage_dart] at hde
    have h2 : (some (some (Delta.toCombMap.alpha e)) : Option (Option Delta.toCombMap.Dart)) =
        some none := hde
    exact Option.some_ne_none _ (Option.some.inj h2)

/-- **The step creates no cell-side dart**, when no relator word has value one. -/
theorem noCellSideDart_step (T : StepData Delta f j family)
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hfree : ∀ x, ¬ CellSideThickening.IsCellSideDart Delta family x) :
    ∀ x, ¬ CellSideThickening.IsCellSideDart (FaceEdgeDoubling.diagram Delta f j hlen hf)
      (stepFamily Delta f j hlen hf T) x := by
  intro x hx
  obtain ⟨⟨C, hC, hCf⟩, hlenx, -, a', ha', hax⟩ := hx
  have hC' : C ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC'
  have hface : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
      FaceEdgeDoubling.faceImage Delta f j hlen C₀.face := hCf
  obtain ⟨b, hb, d, hd, hdx | hdx⟩ :=
    exists_of_mem_stepFamily_sides Delta f j hlen hf T ha' hax
  · have hxe : x = embed Delta.toCombMap (Delta.toCombMap.alpha d) := by
      have h := congrArg (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha hdx
      rw [(FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha_involutive x] at h
      exact h
    subst hxe
    by_cases had : Delta.toCombMap.alpha d = FaceEdgeDoubling.dart Delta f j
    · rw [had, CellHairThickening.faceOf_embed_dart Delta f j hlen hf] at hface
      exact FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen C₀.face hface.symm
    · have hface2 := hface
      rw [CellHairThickening.faceOf_embed Delta f j hlen hf had] at hface2
      have hfd : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = C₀.face :=
        FaceEdgeDoubling.faceImage_injective Delta f j hlen hface2
      have h1 : 1 < (Delta.faceBoundary
          (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d))).darts.length := by
        have h5 := hlenx
        rw [CellHairThickening.faceOf_embed Delta f j hlen hf had,
          FaceEdgeDoubling.boundary_faceImage_darts, List.length_map] at h5
        exact h5
      refine hfree (Delta.toCombMap.alpha d) ⟨⟨C₀, hC₀, hfd⟩, h1, fun c _ => ?_, b, hb, ?_⟩
      · rw [hfd]
        exact CellHairThickening.relatorFace_not_mem hvalue hC₀ c
      · rw [Delta.toCombMap.alpha_involutive d]
        exact hd
  · rw [FaceEdgeDoubling.Holding.dartImage_dart] at hdx
    have hxn : x = none := by
      have h := congrArg (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha hdx
      rw [(FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha_involutive x] at h
      exact h
    subst hxn
    rw [CellHairThickening.faceOf_none Delta f j hlen hf] at hface
    exact FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen C₀.face hface.symm

/-- **The doubling creates no cell hair.** -/
theorem noCellHair_step (hfree : ∀ x, ¬ CellHairThickening.IsCellHair Delta x) :
    ∀ x, ¬ CellHairThickening.IsCellHair (FaceEdgeDoubling.diagram Delta f j hlen hf) x := by
  intro x hx
  obtain ⟨d, -, hd, -⟩ := CellHairThickening.exists_of_isCellHair Delta f j hlen hf hx
  exact hfree d hd

/-- **The doubling creates no cell-edge dart.** -/
theorem noCellEdgeDart_step (hfree : ∀ x, ¬ CellEdgeThickening.IsCellEdgeDart Delta x) :
    ∀ x, ¬ CellEdgeThickening.IsCellEdgeDart (FaceEdgeDoubling.diagram Delta f j hlen hf) x := by
  intro x hx
  obtain ⟨d, -, hd, -⟩ := CellEdgeThickening.exists_of_isCellEdgeDart Delta f j hlen hf hx
  exact hfree d hd

end Doubling

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Induction on the number of region-pair darts, carrying an invariant**, and keeping the absence
of relator words of value one.  Every property of distinguished section families that one doubling
step `sectionFamily` preserves also holds for the output. -/
theorem exists_regionPairFree_of_invariant
    (P : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts → Prop)
    (hP : ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
      (T : StepData S.diagram f j S.family),
      (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) → P S →
        P (RegionPairThickening.sectionFamily S f j hlen hf T))
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) (hS : P S) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsRegionPairDart S'.diagram S'.family x) ∧
          (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
            S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
              (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                (e a).1.2.source.val = a.1.2.source.val ∧
                  (e a).1.2.target.map Fin.val = a.1.2.target.map Fin.val) ∧ P S' := by
  generalize hn : regionPairCount S.diagram S.family = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hdart : ∃ x, IsRegionPairDart S.diagram S.family x
    · obtain ⟨x, hx⟩ := hdart
      obtain ⟨hlen, a, ha, b, hb, hab, hxa, hxb⟩ := hx
      have hf : S.diagram.toCombMap.faceOf x ≠ S.diagram.outerFace :=
        (a.2.boundary.all_gCells _ hxa).1
      obtain ⟨j, hj⟩ := List.get_of_mem
        (((S.diagram.faceBoundary (S.diagram.toCombMap.faceOf x)).mem_iff x).mpr rfl)
      have hdartx : FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j = x := by
        rw [FaceEdgeDoubling.dart_eq_get, hj]
      have hda : S.diagram.toCombMap.faceOf
          (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j) ∈ a.1 := by
        rw [hdartx]
        exact hxa
      have hdb : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
          (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j)) ∈ b.1 := by
        rw [hdartx]
        exact hxb
      have hw : IsRegionPairDart S.diagram S.family
          (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j) := by
        rw [hdartx]
        exact ⟨hlen, a, ha, b, hb, hab, hxa, hxb⟩
      let T : StepData S.diagram (S.diagram.toCombMap.faceOf x) j S.family :=
        stepDataOfPair S.diagram (S.diagram.toCombMap.faceOf x) j S.pairwise hvalue ha hb hab hda hdb
      obtain ⟨S', e, ⟨equiv'⟩, hfree, hvalue', hweight, hprofile, hPS'⟩ :=
        ih _ (lt_of_lt_of_eq (regionPairCount_lt S.diagram _ j hlen hf T S.pairwise hw) hn)
          (RegionPairThickening.sectionFamily S _ j hlen hf T)
          (CellSideThickening.relatorValues_of_step S.diagram _ j hlen hf hvalue)
          (hP S _ j hlen hf T hvalue hS) rfl
      refine ⟨S', (stepEquiv S.diagram _ j hlen hf T).trans e,
        ⟨(FaceEdgeDoubling.oEquivalent S.diagram _ j hlen hf).trans equiv'⟩, hfree, hvalue',
        hweight.trans (stepFamily_weight S.diagram _ j hlen hf T), fun a => ?_, hPS'⟩
      obtain ⟨hprof, hsource, htarget⟩ := hprofile (stepEquiv S.diagram _ j hlen hf T a)
      exact ⟨hprof.trans (stepEquiv_profile S.diagram _ j hlen hf T a),
        hsource.trans (stepEquiv_source S.diagram _ j hlen hf T a),
        htarget.trans (stepEquiv_target S.diagram _ j hlen hf T a)⟩
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, fun x hx => hdart ⟨x, hx⟩, hvalue,
        rfl, fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl)))
          (And.intro rfl rfl), hS⟩

/-- The outer conditions, the cell-side condition and the cell-hair condition, as one invariant of
a family. -/
def RegionsClean (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) : Prop :=
  (∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x) ∧
    (∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x) ∧
      (∀ x, ¬ OuterSideThickening.IsOuterSideDart S.diagram S.family x) ∧
        (∀ x, ¬ CellSideThickening.IsCellSideDart S.diagram S.family x) ∧
          ∀ x, ¬ CellHairThickening.IsCellHair S.diagram x

/-- One doubling step keeps the invariant. -/
theorem regionsClean_of_step (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (T : StepData S.diagram f j S.family)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) (hS : RegionsClean S) :
    RegionsClean (RegionPairThickening.sectionFamily S f j hlen hf T) :=
  ⟨CellSideThickening.noOuterSpur_of_step S.diagram f j hlen hf hS.1,
    CellSideThickening.noOuterCellDart_of_step S.diagram f j hlen hf hS.2.1,
    noOuterSideDart_step S.diagram f j hlen hf T hS.2.2.1,
    noCellSideDart_step S.diagram f j hlen hf T hvalue hS.2.2.2.1,
    noCellHair_step S.diagram f j hlen hf hS.2.2.2.2⟩

end Family

/-- **The `regions` stage of the clean copy, proved.** -/
theorem sectionPocketRegionsCopy : SectionPocketRegionsCopyStatement.{u, w, v} := by
  unfold SectionPocketRegionsCopyStatement
  intro _ _ _ _ _ _ _ _ _ _ S _ hvalue hspur hcell hside hcs hhair
  obtain ⟨S', e, hequiv, hfree, hvalue', hweight, hprofile, hspur', hcell', hside', hcs', hhair'⟩ :=
    exists_regionPairFree_of_invariant RegionsClean
      (fun S f j hlen hf T hvalue hS => regionsClean_of_step S f j hlen hf T hvalue hS) S hvalue
      ⟨hspur, hcell, hside, hcs, hhair⟩
  refine ⟨S', e, hequiv, hvalue', hspur', hcell', hside', hcs', hhair', ?_, hweight,
    fun a => ⟨(hprofile a).1, (hprofile a).2.1⟩⟩
  intro x hx y hy hxy
  exact regions_of_noRegionPairDart hfree hx hy hxy
    (fun _ hdx hdy => one_lt_length_or_of_regions hdx hdy)

end GroupApproximation.GGT.VanKampen.RegionPairThickening

#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.noOuterSideDart_step
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.noCellSideDart_step
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.noCellEdgeDart_step
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.exists_regionPairFree_of_invariant
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.sectionPocketRegionsCopy
