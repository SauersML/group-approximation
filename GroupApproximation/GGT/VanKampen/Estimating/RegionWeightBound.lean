import GroupApproximation.GGT.VanKampen.Estimating.RegionPartition

/-!
# A diagram-independent bound for the actual selection weight

Distinct compatible regions occupy disjoint darts on every relator boundary
and on the outer boundary. Their total weight is therefore bounded by the
sum of those boundary lengths, including both ends of self-contiguities.
O-equivalence preserves this perimeter bound. This
bound permits maximization over diagrams as well as over one diagram's
finite candidate type.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

open scoped Classical

noncomputable def outerArcDarts (a : RegionCandidate D eps Delta) :
    Finset Delta.toCombMap.Dart :=
  if a.2.target = none then a.2.targetArc.darts.toFinset else ∅

theorem outerDarts_nodup (Delta : DiscDiagram.{u, w, v} W) : (outerDarts Delta).Nodup := by
  apply List.Nodup.map Delta.toCombMap.alpha.injective
  exact List.nodup_reverse.mpr (Delta.faceBoundary Delta.outerFace).nodup

theorem outerArcDarts_subset (a : RegionCandidate D eps Delta) :
    a.outerArcDarts ⊆ (outerDarts Delta).toFinset := by
  intro d hd
  simp only [outerArcDarts] at hd
  split at hd
  next ht =>
    have h := a.2.targetArc.mem_cycle_of_mem_darts (List.mem_toFinset.mp hd)
    rw [ht] at h
    exact List.mem_toFinset.mpr h
  next ht => simp at hd

theorem faceOf_mem_of_mem_outerArcDarts (a : RegionCandidate D eps Delta)
    (d : Delta.toCombMap.Dart) (hd : d ∈ a.outerArcDarts) :
    Delta.toCombMap.faceOf d ∈ a.1 := by
  simp only [outerArcDarts] at hd
  split at hd
  next ht =>
    have heq : ∀ (target : Option (Fin Delta.rCellCount))
        (arc : CyclicArc (targetDarts Delta target)), target = none →
          targetBoundaryDarts Delta target arc = arc.darts := by
      intro target arc ht
      subst target
      rfl
    have hm : d ∈ targetBoundaryDarts Delta a.2.target a.2.targetArc := by
      rw [heq _ _ ht]
      exact List.mem_toFinset.mp hd
    have hb : d ∈ a.2.boundary.cycle := by
      rw [a.2.boundary_decomposition]
      simp only [List.mem_append]
      exact Or.inl (Or.inr hm)
    exact ((a.2.boundary.cycle_mem_iff d).mp hb).1
  next ht => simp at hd

theorem outerArcDarts_disjoint {a b : RegionCandidate D eps Delta}
    (hab : Compatible a b) : Disjoint a.outerArcDarts b.outerArcDarts := by
  apply Finset.disjoint_left.mpr
  intro d ha hb
  exact Finset.disjoint_left.mp hab
    (a.faceOf_mem_of_mem_outerArcDarts d ha) (b.faceOf_mem_of_mem_outerArcDarts d hb)

theorem card_outerArcDarts (a : RegionCandidate D eps Delta) :
    a.outerArcDarts.card = if a.2.target = none then a.2.targetArc.length else 0 := by
  by_cases ht : a.2.target = none
  · have hn : (targetDarts Delta a.2.target).Nodup := by
      rw [ht]
      exact outerDarts_nodup Delta
    simp only [outerArcDarts, ht, if_true,
      List.toFinset_card_of_nodup (a.2.targetArc.darts_nodup hn), a.2.targetArc.darts_length]
  · simp only [outerArcDarts, ht, if_false, Finset.card_empty]

theorem weight_eq_cell_and_outer (a : RegionCandidate D eps Delta) :
    a.weight = (∑ i : Fin Delta.rCellCount, (a.cellArcDarts i).card) + a.outerArcDarts.card := by
  cases ht : a.2.target with
  | none =>
      rw [sum_card_cellArcDarts_of_outer a ht, card_outerArcDarts, if_pos ht]
      rfl
  | some j =>
      rw [sum_card_cellArcDarts_of_target a j ht, card_outerArcDarts]
      simp only [ht, Option.some_ne_none, if_false, Nat.add_zero]

theorem sum_cellArcDarts_card_le (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected)
    (i : Fin Delta.rCellCount) :
    (∑ a ∈ selected, (a.cellArcDarts i).card) ≤ (cell Delta i).word.length := by
  have hd : (selected : Set (RegionCandidate D eps Delta)).PairwiseDisjoint
      (fun a => a.cellArcDarts i) := by
    intro a ha b hb hab
    exact cellArcDarts_disjoint (hpairwise a ha b hb hab) i
  rw [← Finset.card_biUnion hd]
  have hsub : (selected.biUnion fun a => a.cellArcDarts i) ⊆ (cellDarts Delta i).toFinset := by
    intro d hd
    obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
    exact a.cellArcDarts_subset i hd
  have hc := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup (cellDarts_nodup Delta i),
    CellBoundaryPartition.cellDarts_length_eq_word_length Delta i] at hc

theorem sum_outerArcDarts_card_le (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) :
    (∑ a ∈ selected, a.outerArcDarts.card) ≤ Delta.boundaryWord.length := by
  have hd : (selected : Set (RegionCandidate D eps Delta)).PairwiseDisjoint
      outerArcDarts := by
    intro a ha b hb hab
    exact outerArcDarts_disjoint (hpairwise a ha b hb hab)
  rw [← Finset.card_biUnion hd]
  have hsub : (selected.biUnion outerArcDarts) ⊆ (outerDarts Delta).toFinset := by
    intro d hd
    obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
    exact a.outerArcDarts_subset hd
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (outerDarts_nodup Delta)] at hc
  have hl := congrArg List.length (dartWord_outerDarts Delta)
  simp only [dartWord, List.length_map] at hl
  rwa [hl] at hc

/-- An actual compatible family's complete weight is bounded by the relator
perimeters and the exterior perimeter, regardless of its G-cell subdivision. -/
theorem familyWeight_le (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) :
    EstimatingSelection.familyWeight weight selected ≤
      (∑ i : Fin Delta.rCellCount, (cell Delta i).word.length) + Delta.boundaryWord.length := by
  unfold EstimatingSelection.familyWeight
  simp only [weight_eq_cell_and_outer, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  exact Nat.add_le_add
    (Finset.sum_le_sum fun i _ => sum_cellArcDarts_card_le selected hpairwise i)
    (sum_outerArcDarts_card_le selected hpairwise)

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.weight_eq_cell_and_outer
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.familyWeight_le
