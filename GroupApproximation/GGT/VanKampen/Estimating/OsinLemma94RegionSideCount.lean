import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSharedEdge
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import GroupApproximation.Meta.AxiomGuard

/-!
# Unbound darts facing a selected region

Osin's proof of Lemma 9.4 (arXiv:math/0411039v3, §9) counts the unbound arcs of type (A1)
on the boundaries of the components.  An unbound dart of a relator cell whose reverse lies in
a selected region is on no side of a component.  Its reverse is on the boundary of the region,
and it is on neither contiguity arc, since a dart of an arc is bound and an outer dart belongs
to no relator cell.  So it is on the left or the right side of the region, and both sides have
at most `ε` darts.  At most `2 ε |M|` unbound darts are lost this way: part of the slack `L n`
of `OsinLemma94RealizedPolygons.Covers`.

* `Embedded.mem_targetBoundaryDarts_cases`: a dart on the target part of a region boundary is
  an outer dart, or the reverse of a dart of the target arc.
* `RealizedSectionFamily.regionFacingUnbound`: the unbound darts of cell `i` whose reverse lies
  in a selected region.
* `RealizedSectionFamily.alpha_mem_sides_of_mem_regionFacingUnbound`: the reverse of such a dart
  is on a side of the region.
* `RealizedSectionFamily.sum_card_regionFacingUnbound_le`: there are at most `2 ε |M|` of them.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Embedded

/-- A dart on the target part of a region boundary: an outer dart when the target is the
exterior, and the reverse of a target-arc dart when the target is a relator cell. -/
theorem mem_targetBoundaryDarts_cases (Delta : DiscDiagram.{u, w, v} W)
    (target : Option (Fin Delta.rCellCount)) (arc : CyclicArc (targetDarts Delta target))
    {x : Delta.toCombMap.Dart} (hx : x ∈ targetBoundaryDarts Delta target arc) :
    (target = none ∧ x ∈ outerDarts Delta) ∨
      ∃ j, target = some j ∧ ∃ e ∈ arc.darts, Delta.toCombMap.alpha e = x := by
  cases target with
  | none =>
    have hx' : x ∈ arc.darts := hx
    exact Or.inl ⟨rfl, arc.mem_cycle_of_mem_darts hx'⟩
  | some j =>
    refine Or.inr ⟨j, rfl, ?_⟩
    have hx' : x ∈ arc.reverseDarts := hx
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hx'
    exact hx'

end Embedded

namespace RealizedSectionFamily

/-- The unbound darts of cell `i` whose reverse lies in a selected region. -/
noncomputable def regionFacingUnbound {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts) (i : Fin S.diagram.rCellCount) :
    Finset S.diagram.toCombMap.Dart :=
  (RegionCandidate.unboundDarts S.family i).filter fun d =>
    ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1

theorem mem_cellDarts_of_mem_regionFacingUnbound {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ S.regionFacingUnbound i) : d ∈ cellDarts S.diagram i :=
  List.mem_toFinset.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hd).1).1

/-- **An unbound dart facing a region lies across a side of it.**  Its reverse is a boundary
dart of the region.  A dart of the source arc, or of a relator-cell target arc, is bound, and
an outer dart is on no relator cell. -/
theorem alpha_mem_sides_of_mem_regionFacingUnbound {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    {i : Fin S.diagram.rCellCount} {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ S.regionFacingUnbound i) :
    ∃ a ∈ S.family, S.diagram.toCombMap.alpha d ∈ a.2.rightSide ++ a.2.leftSide := by
  obtain ⟨hunbound, a, ha, hface⟩ := Finset.mem_filter.mp hd
  have hcell : d ∈ cellDarts S.diagram i := mem_cellDarts_of_mem_regionFacingUnbound S hd
  have hnotBound := (Finset.mem_sdiff.mp hunbound).2
  have hdface : S.diagram.toCombMap.faceOf d = (cell S.diagram i).face :=
    faceOf_of_mem_cellDarts hcell
  have hboundary : IsBoundaryDart S.diagram a.1 (S.diagram.toCombMap.alpha d) := by
    refine ⟨hface, ?_⟩
    rw [S.diagram.toCombMap.alpha_involutive d, hdface]
    exact faces_not_mem_of_value S hvalue a ha _ (cell_mem S.diagram i)
  have hcycle : S.diagram.toCombMap.alpha d ∈ a.2.boundary.cycle :=
    (a.2.boundary.cycle_mem_iff _).mpr hboundary
  have hbound : d ∈ a.cellArcDarts i → False := by
    intro harc
    apply hnotBound
    have hkind : a ∈ RegionCandidate.ofKind S.family a.2.target.isSome :=
      Finset.mem_filter.mpr ⟨ha, rfl⟩
    have hmem : d ∈ RegionCandidate.boundDarts S.family a.2.target.isSome i :=
      Finset.mem_biUnion.mpr ⟨a, hkind, harc⟩
    cases hsome : a.2.target.isSome
    · rw [hsome] at hmem
      exact Finset.mem_union.mpr (Or.inl hmem)
    · rw [hsome] at hmem
      exact Finset.mem_union.mpr (Or.inr hmem)
  rw [a.2.boundary_decomposition] at hcycle
  simp only [List.mem_append] at hcycle
  rcases hcycle with ((hsrc | hright) | htgt) | hleft
  · exfalso
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hsrc
    obtain ⟨e, he, hed⟩ := hsrc
    have hde : e = d := S.diagram.toCombMap.alpha_involutive.injective hed
    have hdarc : d ∈ a.2.sourceArc.darts := hde ▸ he
    have hcells : d ∈ cellDarts S.diagram a.2.source :=
      a.2.sourceArc.mem_cycle_of_mem_darts hdarc
    have hsi : a.2.source = i :=
      cell_face_injective S.diagram ((faceOf_of_mem_cellDarts hcells).symm.trans hdface)
    apply hbound
    unfold RegionCandidate.cellArcDarts
    rw [if_pos hsi]
    simp only [Finset.mem_union, List.mem_toFinset]
    exact Or.inl hdarc
  · exact ⟨a, ha, List.mem_append_left _ hright⟩
  · exfalso
    rcases mem_targetBoundaryDarts_cases S.diagram a.2.target a.2.targetArc htgt with
      ⟨_, hout⟩ | ⟨j, hj, e, he, hed⟩
    · have hdOuter : S.diagram.toCombMap.faceOf d = S.diagram.outerFace := by
        simp only [outerDarts, List.mem_map, List.mem_reverse] at hout
        obtain ⟨e, he, hed⟩ := hout
        rw [← S.diagram.toCombMap.alpha_involutive.injective hed]
        exact ((S.diagram.faceBoundary S.diagram.outerFace).mem_iff e).mp he
      exact (cell S.diagram i).face_ne_outer (hdface.symm.trans hdOuter)
    · have hde : e = d := S.diagram.toCombMap.alpha_involutive.injective hed
      have hdarc : d ∈ a.2.targetArc.darts := hde ▸ he
      have hcyc : d ∈ targetDarts S.diagram a.2.target :=
        a.2.targetArc.mem_cycle_of_mem_darts hdarc
      rw [hj] at hcyc
      have hcellj : d ∈ cellDarts S.diagram j := hcyc
      have hji : j = i :=
        cell_face_injective S.diagram ((faceOf_of_mem_cellDarts hcellj).symm.trans hdface)
      apply hbound
      unfold RegionCandidate.cellArcDarts
      rw [if_pos (hj.trans (congrArg some hji))]
      simp only [Finset.mem_union, List.mem_toFinset]
      exact Or.inr hdarc
  · exact ⟨a, ha, List.mem_append_right _ hleft⟩

/-- **The region-side count.**  The unbound darts facing a selected region are at most
`2 ε |M|`: `alpha` maps them injectively into the sides of the regions, and each side has at
most `ε` darts. -/
theorem sum_card_regionFacingUnbound_le {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) :
    ∑ i : Fin S.diagram.rCellCount, (S.regionFacingUnbound i).card ≤ 2 * eps * S.family.card := by
  have hdisj : ((Finset.univ : Finset (Fin S.diagram.rCellCount)) :
      Set (Fin S.diagram.rCellCount)).PairwiseDisjoint fun i => S.regionFacingUnbound i := by
    intro i _ j _ hij
    exact Finset.disjoint_left.mpr fun d hdi hdj => hij (cell_face_injective S.diagram
      ((faceOf_of_mem_cellDarts (mem_cellDarts_of_mem_regionFacingUnbound S hdi)).symm.trans
        (faceOf_of_mem_cellDarts (mem_cellDarts_of_mem_regionFacingUnbound S hdj))))
  calc ∑ i : Fin S.diagram.rCellCount, (S.regionFacingUnbound i).card
      = (Finset.univ.biUnion fun i => S.regionFacingUnbound i).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (S.family.biUnion fun a => (a.2.rightSide ++ a.2.leftSide).toFinset).card := by
        refine Finset.card_le_card_of_injOn S.diagram.toCombMap.alpha ?_ ?_
        · intro d hd
          obtain ⟨i, _, hdi⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hd)
          obtain ⟨a, ha, hside⟩ := alpha_mem_sides_of_mem_regionFacingUnbound S hvalue hdi
          exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨a, ha, List.mem_toFinset.mpr hside⟩)
        · intro d _ e _ hde
          exact S.diagram.toCombMap.alpha_involutive.injective hde
    _ ≤ ∑ a ∈ S.family, (a.2.rightSide ++ a.2.leftSide).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S.family, 2 * eps := by
        apply Finset.sum_le_sum
        intro a _
        calc (a.2.rightSide ++ a.2.leftSide).toFinset.card
            ≤ (a.2.rightSide ++ a.2.leftSide).length := List.toFinset_card_le ..
          _ ≤ 2 * eps := by
              rw [List.length_append]
              have h1 := a.2.rightSide_length_le
              have h2 := a.2.leftSide_length_le
              omega
    _ = 2 * eps * S.family.card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

end RealizedSectionFamily

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.mem_targetBoundaryDarts_cases
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.regionFacingUnbound
#audit_axioms
  GroupApproximation.GGT.VanKampen.RealizedSectionFamily.mem_cellDarts_of_mem_regionFacingUnbound
#audit_axioms
  GroupApproximation.GGT.VanKampen.RealizedSectionFamily.alpha_mem_sides_of_mem_regionFacingUnbound
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.sum_card_regionFacingUnbound_le

end GroupApproximation.GGT.VanKampen
