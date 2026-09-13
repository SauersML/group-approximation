import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94RegionSideCount
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the short sides of the polygons number at most `2 ε |M|`

Osin (math/0411039v3, §9), before Lemma 9.3: "(A3) A side arc of some ε-contiguity subdiagram
from M."  Proof of Lemma 9.3: "Clearly the number of arcs of type (A3) is at most 2|M| = 2e ≤
24n."

This module counts the (A3) sides of `OsinLemma94RealizedPolygons S`, not Osin's arcs.  One
side arc of a region can be split among several polygon sides, so the bound is `2 ε |M|` in
place of `2|M|`.  That is enough for `OsinLemma94PolygonSideBudgetInput`, where `K` is chosen
after `ε`.

A side of type (A3) of a polygon `P.face k` runs along the faces of one selected region `a`.
The reverse of each of its darts is a boundary dart of `a`: the polygon's face lies in no
selected region.  On the boundary cycle of `a` it is on neither contiguity arc, since the
polygon's face is no relator cell, and not on `∂Δ`, since the polygon's face is not the outer
face.  So it is on the left or the right side of `a`, each of at most `ε` darts.  The sides of
the polygons are disjoint and nonempty, so there are at most `2 ε |M|` short sides.

* `OsinLemma94RealizedPolygons.shortSides`: the sides of polygon `k` of type (A3).
* `OsinLemma94RealizedPolygons.alpha_mem_sides_of_short`: the reverse of a dart of a short side
  is on a side of a selected region.
* `OsinLemma94RealizedPolygons.sum_card_shortSides_le`: there are at most `2 ε |M|` short sides.
* `OsinLemma94RealizedPolygons.sum_card_shortSides_le_mul`: with `|M| ≤ 3 (n + r - 1)`, at most
  `24 ε n`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The sides of polygon `k` of type (A3). -/
noncomputable def shortSides (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (Finset.range (P.sideCount k)).filter fun i => P.kind k i = .short

/-- A dart of a side of polygon `k` lies on the face of polygon `k`. -/
theorem faceOf_of_mem_sideDarts (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {i : ℕ}
    (hi : i < P.sideCount k) {d : S.diagram.toCombMap.Dart} (hd : d ∈ P.sideDarts k i) :
    S.diagram.toCombMap.faceOf d = P.face k := by
  have hmem : d ∈ (S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k) := by
    rw [P.walk k]
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hd⟩
  exact ((S.diagram.faceBoundary (P.face k)).mem_iff d).mp (List.mem_rotate.mp hmem)

/-- Two different sides of one polygon have no common dart, since the face walk has no repeated
dart. -/
theorem sideDarts_disjoint (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {i j : ℕ}
    (hi : i < P.sideCount k) (hj : j < P.sideCount k) (hij : i ≠ j) :
    List.Disjoint (P.sideDarts k i) (P.sideDarts k j) := by
  have hnodup : ((List.range (P.sideCount k)).flatMap (P.sideDarts k)).Nodup := by
    rw [← P.walk k]
    exact List.nodup_rotate.mpr (S.diagram.faceBoundary (P.face k)).nodup
  have hpair := List.pairwise_iff_getElem.mp (List.nodup_flatMap.mp hnodup).2
  have key : ∀ a b, a < b → b < P.sideCount k →
      List.Disjoint (P.sideDarts k a) (P.sideDarts k b) := by
    intro a b hab hb
    have h := hpair a b (by rw [List.length_range]; omega) (by rw [List.length_range]; omega)
      hab
    simpa only [Function.onFun, List.getElem_range] using h
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h hj
  · exact (key j i h hi).symm

/-- **A dart of a short side lies across a side of a selected region.**  Its reverse is a
boundary dart of the region, since the polygon's face is in no selected region.  It is on
neither contiguity arc, since the polygon's face is no relator cell, and it is no outer dart,
since the polygon's face is not the outer face. -/
theorem alpha_mem_sides_of_short (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {i : ℕ}
    (hi : i < P.sideCount k) (hkind : P.kind k i = .short) {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ P.sideDarts k i) :
    ∃ a ∈ S.family, S.diagram.toCombMap.alpha d ∈ a.2.rightSide ++ a.2.leftSide := by
  obtain ⟨a, ha, hall⟩ := P.short_region k i hi hkind
  have hdk := P.faceOf_of_mem_sideDarts hi hd
  have hboundary : IsBoundaryDart S.diagram a.1 (S.diagram.toCombMap.alpha d) := by
    refine ⟨hall d hd, ?_⟩
    rw [S.diagram.toCombMap.alpha_involutive d, hdk]
    exact P.face_unselected k a ha
  have hcycle : S.diagram.toCombMap.alpha d ∈ a.2.boundary.cycle :=
    (a.2.boundary.cycle_mem_iff _).mpr hboundary
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
    exact P.face_not_cell k a.2.source ((faceOf_of_mem_cellDarts hcells).symm.trans hdk)
  · exact ⟨a, ha, List.mem_append_left _ hright⟩
  · exfalso
    rcases mem_targetBoundaryDarts_cases S.diagram a.2.target a.2.targetArc htgt with
      ⟨_, hout⟩ | ⟨j, hj, e, he, hed⟩
    · simp only [outerDarts, List.mem_map, List.mem_reverse] at hout
      obtain ⟨e, he, hed⟩ := hout
      rw [S.diagram.toCombMap.alpha_involutive.injective hed] at he
      exact P.face_ne_outer k
        (hdk.symm.trans (((S.diagram.faceBoundary S.diagram.outerFace).mem_iff d).mp he))
    · have hde : e = d := S.diagram.toCombMap.alpha_involutive.injective hed
      have hdarc : d ∈ a.2.targetArc.darts := hde ▸ he
      have hcyc : d ∈ targetDarts S.diagram a.2.target :=
        a.2.targetArc.mem_cycle_of_mem_darts hdarc
      rw [hj] at hcyc
      have hcellj : d ∈ cellDarts S.diagram j := hcyc
      exact P.face_not_cell k j ((faceOf_of_mem_cellDarts hcellj).symm.trans hdk)
  · exact ⟨a, ha, List.mem_append_right _ hleft⟩

/-- **The short sides number at most `2 ε |M|`.**  `alpha` maps the darts of the short sides
injectively into the sides of the selected regions, each of at most `ε` darts.  Different sides
have no common dart, and every side has a dart. -/
theorem sum_card_shortSides_le (P : OsinLemma94RealizedPolygons S) :
    ∑ k, (P.shortSides k).card ≤ 2 * eps * S.family.card := by
  let T : Fin P.count → Finset S.diagram.toCombMap.Dart := fun k =>
    (P.shortSides k).biUnion fun i => (P.sideDarts k i).toFinset
  have hmemT : ∀ k d, d ∈ T k →
      ∃ i, i < P.sideCount k ∧ P.kind k i = .short ∧ d ∈ P.sideDarts k i := by
    intro k d hd
    obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨hir, hkind⟩ := Finset.mem_filter.mp hi
    exact ⟨i, Finset.mem_range.mp hir, hkind, List.mem_toFinset.mp hdi⟩
  have hsides : ∀ k, (P.shortSides k).card ≤ (T k).card := by
    intro k
    have hdisj : ((P.shortSides k : Finset ℕ) : Set ℕ).PairwiseDisjoint
        fun i => (P.sideDarts k i).toFinset := by
      intro i hi j hj hij
      have hi' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
      have hj' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1
      exact Finset.disjoint_left.mpr fun d hdi hdj =>
        P.sideDarts_disjoint k hi' hj' hij (List.mem_toFinset.mp hdi) (List.mem_toFinset.mp hdj)
    calc (P.shortSides k).card = ∑ _i ∈ P.shortSides k, 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ i ∈ P.shortSides k, (P.sideDarts k i).toFinset.card :=
          Finset.sum_le_sum fun i hi => Finset.one_le_card.mpr ⟨_, List.mem_toFinset.mpr
            (List.head_mem (P.side_ne_nil k i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)))⟩
      _ = (T k).card := (Finset.card_biUnion hdisj).symm
  have hface : ∀ k d, d ∈ T k → S.diagram.toCombMap.faceOf d = P.face k := by
    intro k d hd
    obtain ⟨i, hi, -, hdi⟩ := hmemT k d hd
    exact P.faceOf_of_mem_sideDarts hi hdi
  have hdisjT :
      ((Finset.univ : Finset (Fin P.count)) : Set (Fin P.count)).PairwiseDisjoint T := by
    intro k _ k' _ hkk'
    exact Finset.disjoint_left.mpr fun d hd hd' =>
      hkk' (P.face_injective ((hface k d hd).symm.trans (hface k' d hd')))
  calc ∑ k, (P.shortSides k).card
      ≤ ∑ k, (T k).card := Finset.sum_le_sum fun k _ => hsides k
    _ = (Finset.univ.biUnion T).card := (Finset.card_biUnion hdisjT).symm
    _ ≤ (S.family.biUnion fun a => (a.2.rightSide ++ a.2.leftSide).toFinset).card := by
        refine Finset.card_le_card_of_injOn S.diagram.toCombMap.alpha ?_
          S.diagram.toCombMap.alpha_involutive.injective.injOn
        intro d hd
        obtain ⟨k, -, hdk⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hd)
        obtain ⟨i, hi, hkind, hdi⟩ := hmemT k d hdk
        obtain ⟨a, ha, hside⟩ := P.alpha_mem_sides_of_short hi hkind hdi
        exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨a, ha, List.mem_toFinset.mpr hside⟩)
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

/-- **The short sides number at most `24 ε n`**, when `|M| ≤ 3 (n + r - 1)` with `n ≥ 1`
relator cells and at most four sections. -/
theorem sum_card_shortSides_le_mul (P : OsinLemma94RealizedPolygons S)
    (hcells : 0 < Delta.rCellCount)
    (hcard : S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)) :
    ∑ k, (P.shortSides k).card ≤ 24 * eps * Delta.rCellCount := by
  have hfam : S.family.card ≤ 12 * Delta.rCellCount := by
    have := cuts.count_le
    omega
  calc _ ≤ 2 * eps * S.family.card := P.sum_card_shortSides_le
    _ ≤ 2 * eps * (12 * Delta.rCellCount) := Nat.mul_le_mul le_rfl hfam
    _ = 24 * eps * Delta.rCellCount := by ring

end OsinLemma94RealizedPolygons

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.shortSides
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.faceOf_of_mem_sideDarts
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.sideDarts_disjoint
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.alpha_mem_sides_of_short
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.sum_card_shortSides_le
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.sum_card_shortSides_le_mul

end GroupApproximation.GGT.VanKampen
