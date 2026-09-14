import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningStep
import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# The region-pair thickening removes a region-pair dart and creates none

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  This file supplies the induction of the
region-pair thickening with its three combinatorial inputs.

* `one_lt_length_or_of_regions`: an edge from a face of one region to a face of another has a face
  with at least two darts on one side.  Otherwise both faces are monogons, the vertex rotation swaps
  the two darts of the edge, and the connected map has only those two darts, so the exterior would
  be a face of a region.  This discharges the hypothesis `hmono` of `regions_of_noRegionPairDart`.
* `side_of_pair`, `familyArcAvoid_of_pair`, `stepDataOfPair`: at a region-pair dart, when no
  relator word has value one, the dart lies on a side of its region and in no arc of any other
  region.
* `exists_of_isRegionPairDart_step`, `regionPairCount_lt`: a region-pair dart after the step is the
  image of an old one other than `w_j`, so the count drops.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.RegionPairThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Basics

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- A face with at most one dart is fixed by face rotation. -/
theorem facePerm_eq_self_of_length_le_one {d : Delta.toCombMap.Dart}
    (h : (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length ≤ 1) :
    Delta.toCombMap.facePerm d = d := by
  have hd : d ∈ (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts :=
    ((Delta.faceBoundary _).mem_iff d).mpr rfl
  have he : Delta.toCombMap.facePerm d ∈ (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts :=
    ((Delta.faceBoundary _).mem_iff _).mpr (Delta.toCombMap.faceOf_facePerm d)
  rcases hl : (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts with _ | ⟨a, _ | ⟨b, t⟩⟩
  · rw [hl] at hd
    simp at hd
  · rw [hl] at hd he
    rw [List.mem_singleton.mp he, List.mem_singleton.mp hd]
  · rw [hl] at h
    simp at h

/-- **An edge between two regions has a face with at least two darts.** -/
theorem one_lt_length_or_of_regions {x y : RegionCandidate D eps Delta} {d : Delta.toCombMap.Dart}
    (hdx : Delta.toCombMap.faceOf d ∈ x.1)
    (hdy : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ y.1) :
    1 < (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length ∨
      1 < (Delta.faceBoundary
        (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d))).darts.length := by
  by_contra hno
  have h1 : (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length ≤ 1 := by
    by_contra h
    exact hno (Or.inl (by omega))
  have h2 : (Delta.faceBoundary
      (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d))).darts.length ≤ 1 := by
    by_contra h
    exact hno (Or.inr (by omega))
  have hf1 := facePerm_eq_self_of_length_le_one h1
  have hf2 := facePerm_eq_self_of_length_le_one h2
  have hs1 : Delta.toCombMap.sigma d = Delta.toCombMap.alpha d := by
    have hp : Delta.toCombMap.facePerm (Delta.toCombMap.alpha d) =
        Delta.toCombMap.sigma (Delta.toCombMap.alpha (Delta.toCombMap.alpha d)) := rfl
    rw [Delta.toCombMap.alpha_involutive d] at hp
    rw [← hp, hf2]
  have hs2 : Delta.toCombMap.sigma (Delta.toCombMap.alpha d) = d := by
    have hp : Delta.toCombMap.facePerm d = Delta.toCombMap.sigma (Delta.toCombMap.alpha d) := rfl
    rw [← hp, hf1]
  have hclosed : ∀ a b : Delta.toCombMap.Dart, Relation.EqvGen Delta.toCombMap.Adjacent a b →
      ((a = d ∨ a = Delta.toCombMap.alpha d) ↔ (b = d ∨ b = Delta.toCombMap.alpha d)) := by
    intro a b hab
    induction hab with
    | rel a b h =>
      rcases h with h | h
      · subst h
        constructor
        · rintro (rfl | rfl)
          · exact Or.inr rfl
          · exact Or.inl (Delta.toCombMap.alpha_involutive d)
        · rintro (h | h)
          · right
            rw [← h, Delta.toCombMap.alpha_involutive a]
          · left
            exact Delta.toCombMap.alpha_involutive.injective h
      · subst h
        constructor
        · rintro (rfl | rfl)
          · exact Or.inr hs1
          · exact Or.inl hs2
        · rintro (h | h)
          · right
            exact Delta.toCombMap.sigma.injective (h.trans hs2.symm)
          · left
            exact Delta.toCombMap.sigma.injective (h.trans hs1.symm)
    | refl => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  obtain ⟨o, r, hor⟩ := List.exists_cons_of_ne_nil (Delta.faceBoundary Delta.outerFace).nonempty
  have ho : o ∈ (Delta.faceBoundary Delta.outerFace).darts := by
    rw [hor]
    simp
  have hoface : Delta.toCombMap.faceOf o = Delta.outerFace :=
    ((Delta.faceBoundary _).mem_iff o).mp ho
  rcases (hclosed d o (Delta.planar.1 d o)).mp (Or.inl rfl) with rfl | rfl
  · exact (x.2.boundary.all_gCells _ hdx).1 hoface
  · exact (y.2.boundary.all_gCells _ hdy).1 hoface

/-- A dart of a target arc on the boundary of a region crosses into the exterior or a cell. -/
theorem faceOf_alpha_of_mem_targetBoundaryDarts' {target : Option (Fin Delta.rCellCount)}
    (arc : CyclicArc (targetDarts Delta target)) {d : Delta.toCombMap.Dart}
    (hd : d ∈ targetBoundaryDarts Delta target arc) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = Delta.outerFace ∨
      ∃ k : Fin Delta.rCellCount, Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = (cell Delta k).face := by
  cases target with
  | none =>
    left
    have hdo : d ∈ outerDarts Delta := arc.mem_cycle_of_mem_darts hd
    simp only [outerDarts, List.mem_map, List.mem_reverse] at hdo
    obtain ⟨e, he, rfl⟩ := hdo
    rw [Delta.toCombMap.alpha_involutive e]
    exact ((Delta.faceBoundary Delta.outerFace).mem_iff e).mp he
  | some k =>
    right
    refine ⟨k, ?_⟩
    have hs : d ∈ arc.reverseDarts := hd
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hs
    obtain ⟨e, he, rfl⟩ := hs
    rw [Delta.toCombMap.alpha_involutive e]
    exact ((Delta.faceBoundary (cell Delta k).face).mem_iff e).mp (arc.mem_cycle_of_mem_darts he)

/-- **At an edge between two disjoint regions, the dart lies on a side of its region**, when no
relator word has value one. -/
theorem side_of_pair {a b : RegionCandidate D eps Delta} (hab : Disjoint a.1 b.1)
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1) {d : Delta.toCombMap.Dart}
    (hda : Delta.toCombMap.faceOf d ∈ a.1)
    (hdb : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ b.1) :
    d ∈ a.2.rightSide ++ a.2.leftSide := by
  have hcyc := (a.2.boundary.cycle_mem_iff d).mpr
    ⟨hda, fun h => Finset.disjoint_left.mp hab h hdb⟩
  rw [a.2.boundary_decomposition] at hcyc
  rcases List.mem_append.mp hcyc with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exfalso
        simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at h1
        obtain ⟨e, he, rfl⟩ := h1
        rw [Delta.toCombMap.alpha_involutive e,
          faceOf_of_mem_cellDarts (a.2.sourceArc.mem_cycle_of_mem_darts he)] at hdb
        exact CellHairThickening.relatorFace_not_mem hvalue (cell_mem Delta a.2.source) b hdb
      · exact List.mem_append_left _ h2
    · exfalso
      rcases faceOf_alpha_of_mem_targetBoundaryDarts' a.2.targetArc h3 with h | ⟨k, h⟩
      · rw [h] at hdb
        exact (b.2.boundary.all_gCells _ hdb).1 rfl
      · rw [h] at hdb
        exact CellHairThickening.relatorFace_not_mem hvalue (cell_mem Delta k) b hdb
  · exact List.mem_append_right _ h4

end Basics

section Doubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}
  (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

variable {family : Finset (RegionCandidate D eps Delta)}

/-- **At an edge between two regions, no other region uses the dart in an arc**, when no relator
word has value one. -/
theorem familyArcAvoid_of_pair
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family)
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1)
    {a b : RegionCandidate D eps Delta} (ha : a ∈ family)
    (hda : Delta.toCombMap.faceOf (FaceEdgeDoubling.dart Delta f j) ∈ a.1)
    (hdb : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∈ b.1) :
    FaceEdgeDoubling.FamilyArcAvoid Delta f j (family.erase a) := by
  intro c hc
  have hcS := Finset.mem_of_mem_erase hc
  have hca : c ≠ a := Finset.ne_of_mem_erase hc
  have hfa : f ∈ a.1 := by
    rw [FaceEdgeDoubling.dart_face] at hda
    exact hda
  refine ⟨fun hfc => Finset.disjoint_left.mp (hcompat c hcS a ha hca) hfc hfa, fun hsrc => ?_,
    fun htgt => ?_⟩
  · have hface := faceOf_of_mem_cellDarts (c.2.sourceArc.mem_cycle_of_mem_darts hsrc)
    rw [FaceEdgeDoubling.dart_face] at hface
    exact CellHairThickening.relatorFace_not_mem hvalue (cell_mem Delta c.2.source) a (hface ▸ hfa)
  · rcases FaceEdgeDoubling.mem_targetBoundaryDarts_of_mem Delta c.2.target c.2.targetArc htgt with
      h | h
    · rcases faceOf_alpha_of_mem_targetBoundaryDarts' c.2.targetArc h with ho | ⟨k, hk⟩
      · rw [ho] at hdb
        exact (b.2.boundary.all_gCells _ hdb).1 rfl
      · rw [hk] at hdb
        exact CellHairThickening.relatorFace_not_mem hvalue (cell_mem Delta k) b hdb
    · rcases faceOf_alpha_of_mem_targetBoundaryDarts' c.2.targetArc h with ho | ⟨k, hk⟩
      · rw [Delta.toCombMap.alpha_involutive] at ho
        rw [ho] at hda
        exact (a.2.boundary.all_gCells _ hda).1 rfl
      · rw [Delta.toCombMap.alpha_involutive] at hk
        rw [hk] at hda
        exact CellHairThickening.relatorFace_not_mem hvalue (cell_mem Delta k) a hda

/-- **The step data at a region-pair dart.** -/
noncomputable def stepDataOfPair
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family)
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1)
    {a b : RegionCandidate D eps Delta} (ha : a ∈ family) (hb : b ∈ family) (hab : a ≠ b)
    (hda : Delta.toCombMap.faceOf (FaceEdgeDoubling.dart Delta f j) ∈ a.1)
    (hdb : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∈ b.1) :
    StepData Delta f j family where
  holder := a
  holder_mem := ha
  side := side_of_pair (hcompat a ha b hb hab) hvalue hda hdb
  avoid := familyArcAvoid_of_pair Delta f j hcompat hvalue ha hda hdb

/-- The faces of a region after the step are the images of the faces of an old region. -/
theorem mem_stepFamily_faces (T : StepData Delta f j family)
    {a' : RegionCandidate D eps (FaceEdgeDoubling.diagram Delta f j hlen hf)}
    (ha' : a' ∈ stepFamily Delta f j hlen hf T) :
    ∃ a ∈ family, ∀ F, F ∈ a'.1 ↔
      ∃ g ∈ a.1, FaceEdgeDoubling.faceImage Delta f j hlen g = F := by
  rcases Finset.mem_insert.mp ha' with rfl | ha''
  · exact ⟨T.holder, T.holder_mem, fun F => Finset.mem_map⟩
  · obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp ha''
    refine ⟨b.val, Finset.mem_of_mem_erase b.property, fun F => ?_⟩
    change F ∈ b.val.1.map (FaceEdgeDoubling.embedding Delta f j hlen hf).faces ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, FaceEdgeDoubling.faceImage_of_ne Delta f j hlen
        (fun h => (T.avoid b.val b.property).1 (h ▸ hg))⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, (FaceEdgeDoubling.faceImage_of_ne Delta f j hlen
        (fun h => (T.avoid b.val b.property).1 (h ▸ hg))).symm⟩

/-- **A region-pair dart after the step is the image of an old region-pair dart other than
`w_j`.** -/
theorem exists_of_isRegionPairDart_step (T : StepData Delta f j family)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family)
    {x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hx : IsRegionPairDart (FaceEdgeDoubling.diagram Delta f j hlen hf)
      (stepFamily Delta f j hlen hf T) x) :
    ∃ e, embed Delta.toCombMap e = x ∧ IsRegionPairDart Delta family e ∧
      e ≠ FaceEdgeDoubling.dart Delta f j := by
  obtain ⟨hlenx, a', ha', b', hb', hne', hxa', hxb'⟩ := hx
  obtain ⟨a, ha, hfa⟩ := mem_stepFamily_faces Delta f j hlen hf T ha'
  obtain ⟨b, hb, hfb⟩ := mem_stepFamily_faces Delta f j hlen hf T hb'
  obtain ⟨g, hg, hgx⟩ := (hfa _).mp hxa'
  obtain ⟨e, hef, hex⟩ : ∃ e, Delta.toCombMap.faceOf e = g ∧
      FaceEdgeDoubling.dartImage Delta f j hlen e = x := by
    by_cases hgf : g = f
    · rw [hgf, FaceEdgeDoubling.faceImage_self] at hgx
      obtain ⟨d, hd, hdx⟩ := CellHairThickening.exists_of_faceOf_eq_cellFace Delta f j hlen hf hgx.symm
      exact ⟨d, hd.trans hgf.symm, hdx⟩
    · rw [FaceEdgeDoubling.faceImage_of_ne Delta f j hlen hgf] at hgx
      obtain ⟨d, hd, hdx⟩ := CellHairThickening.exists_of_faceOf_eq_keep Delta f j hlen hf hgf hgx.symm
      have hdne : d ≠ FaceEdgeDoubling.dart Delta f j := by
        intro heq
        rw [heq, FaceEdgeDoubling.dart_face] at hd
        exact hgf hd.symm
      exact ⟨d, hd, (FaceEdgeDoubling.Holding.dartImage_of_ne Delta f j hlen hdne).trans hdx⟩
  obtain ⟨g', hg', hg'x⟩ := (hfb _).mp hxb'
  have hne : e ≠ FaceEdgeDoubling.dart Delta f j := by
    intro heq
    rw [heq, FaceEdgeDoubling.Holding.dartImage_dart] at hex
    rw [← hex] at hg'x
    exact FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen g'
      (hg'x.trans (CellHairThickening.faceOf_none Delta f j hlen hf))
  have hxe : embed Delta.toCombMap e = x :=
    (FaceEdgeDoubling.Holding.dartImage_of_ne Delta f j hlen hne).symm.trans hex
  rw [← hxe] at hg'x
  have hane : Delta.toCombMap.alpha e ≠ FaceEdgeDoubling.dart Delta f j := by
    intro heq
    have h2 := congrArg (fun y => (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf
      (embed Delta.toCombMap y)) heq
    exact FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen g'
      ((hg'x.trans h2).trans (CellHairThickening.faceOf_embed_dart Delta f j hlen hf))
  have hfae : Delta.toCombMap.faceOf (Delta.toCombMap.alpha e) = g' :=
    (FaceEdgeDoubling.faceImage_injective Delta f j hlen
      (hg'x.trans (CellHairThickening.faceOf_embed Delta f j hlen hf hane))).symm
  have hab : a ≠ b := by
    intro hab
    subst hab
    have h1 : FaceEdgeDoubling.faceImage Delta f j hlen g' ∈ a'.1 := (hfa _).mpr ⟨g', hg', rfl⟩
    have h2 : FaceEdgeDoubling.faceImage Delta f j hlen g' ∈ b'.1 := (hfb _).mpr ⟨g', hg', rfl⟩
    exact Finset.disjoint_left.mp
      (stepFamily_pairwise Delta f j hlen hf T hcompat a' ha' b' hb' hne') h1 h2
  have hlen_e : 1 < (Delta.faceBoundary (Delta.toCombMap.faceOf e)).darts.length := by
    have h4 : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
        FaceEdgeDoubling.faceImage Delta f j hlen (Delta.toCombMap.faceOf e) := by
      rw [← hxe]
      exact CellHairThickening.faceOf_embed Delta f j hlen hf hne
    have h5 := hlenx
    rw [h4, FaceEdgeDoubling.boundary_faceImage_darts, List.length_map] at h5
    exact h5
  exact ⟨e, hxe, ⟨hlen_e, a, ha, b, hb, hab, hef ▸ hg, hfae ▸ hg'⟩, hne⟩

/-- **The step removes the region-pair dart `w_j` and creates none.** -/
theorem regionPairCount_lt (T : StepData Delta f j family)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family)
    (hw : IsRegionPairDart Delta family (FaceEdgeDoubling.dart Delta f j)) :
    regionPairCount (FaceEdgeDoubling.diagram Delta f j hlen hf)
        (stepFamily Delta f j hlen hf T) < regionPairCount Delta family := by
  have hmem : FaceEdgeDoubling.dart Delta f j ∈
      Finset.univ.filter (IsRegionPairDart Delta family) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
  unfold regionPairCount
  refine lt_of_le_of_lt ?_ (Finset.card_erase_lt_of_mem hmem)
  refine Finset.card_le_card_of_injOn
    (fun x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart =>
      (Option.bind x id).getD (FaceEdgeDoubling.dart Delta f j)) ?_ ?_
  · intro x hx
    obtain ⟨e, rfl, he, hne⟩ := exists_of_isRegionPairDart_step Delta f j hlen hf T hcompat
      (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    exact Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩)
  · intro x hx y hy hxy
    obtain ⟨d, rfl, -, -⟩ := exists_of_isRegionPairDart_step Delta f j hlen hf T hcompat
      (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    obtain ⟨e, rfl, -, -⟩ := exists_of_isRegionPairDart_step Delta f j hlen hf T hcompat
      (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    exact congrArg (embed Delta.toCombMap) hxy

end Doubling

end GroupApproximation.GGT.VanKampen.RegionPairThickening

#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.one_lt_length_or_of_regions
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.side_of_pair
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.familyArcAvoid_of_pair
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.exists_of_isRegionPairDart_step
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.regionPairCount_lt
