import GroupApproximation.GGT.VanKampen.Estimating.RegionCandidate
import GroupApproximation.GGT.VanKampen.Estimating.Partition

/-!
# Boundary counts allowing self-contiguities

A cell receives the union of a region's source and target arcs. When both
ends lie on the same cell, boundary simplicity separates the actual darts,
so their lengths add. Face disjointness separates different selected regions.
No distinct-target or O52 certificate is used in these counting identities.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

open scoped Classical

/-- The actual darts of this region on one indexed cell. -/
noncomputable def cellArcDarts (a : RegionCandidate D eps Delta)
    (i : Fin Delta.rCellCount) : Finset Delta.toCombMap.Dart := by
  classical
  exact (if a.2.source = i then a.2.sourceArc.darts.toFinset else ∅) ∪
    (if a.2.target = some i then a.2.targetArc.darts.toFinset else ∅)

theorem cellArcDarts_subset (a : RegionCandidate D eps Delta)
    (i : Fin Delta.rCellCount) :
    a.cellArcDarts i ⊆ (cellDarts Delta i).toFinset := by
  classical
  intro d hd
  rcases Finset.mem_union.mp hd with hs | ht
  · split at hs
    next heq =>
      have h := a.2.sourceArc.mem_cycle_of_mem_darts (List.mem_toFinset.mp hs)
      rw [heq] at h
      exact List.mem_toFinset.mpr h
    next heq => simp at hs
  · split at ht
    next heq =>
      have h := a.2.targetArc.mem_cycle_of_mem_darts (List.mem_toFinset.mp ht)
      rw [heq] at h
      exact List.mem_toFinset.mpr h
    next heq => simp at ht

theorem faceOf_alpha_mem_of_mem_cellArcDarts
    (a : RegionCandidate D eps Delta) (i : Fin Delta.rCellCount)
    (d : Delta.toCombMap.Dart) (hd : d ∈ a.cellArcDarts i) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ a.1 := by
  classical
  rcases Finset.mem_union.mp hd with hs | ht
  · split at hs
    next heq => exact a.2.faceOf_alpha_mem_of_mem_sourceArc d (List.mem_toFinset.mp hs)
    next heq => simp at hs
  · split at ht
    next heq => exact a.2.faceOf_alpha_mem_of_mem_targetArc i heq d (List.mem_toFinset.mp ht)
    next heq => simp at ht

theorem cellArcDarts_disjoint {a b : RegionCandidate D eps Delta}
    (hab : Compatible a b) (i : Fin Delta.rCellCount) :
    Disjoint (a.cellArcDarts i) (b.cellArcDarts i) := by
  classical
  apply Finset.disjoint_left.mpr
  intro d ha hb
  exact Finset.disjoint_left.mp hab
    (a.faceOf_alpha_mem_of_mem_cellArcDarts i d ha)
    (b.faceOf_alpha_mem_of_mem_cellArcDarts i d hb)

/-- Each end contributes its own stored length, exactly at its own cell. -/
theorem card_cellArcDarts (a : RegionCandidate D eps Delta)
    (i : Fin Delta.rCellCount) :
    (a.cellArcDarts i).card =
      (if a.2.source = i then a.2.sourceArc.length else 0) +
      (if a.2.target = some i then a.2.targetArc.length else 0) := by
  classical
  have hslen : a.2.sourceArc.darts.toFinset.card = a.2.sourceArc.length := by
    rw [List.toFinset_card_of_nodup
      (a.2.sourceArc.darts_nodup (cellDarts_nodup Delta a.2.source)),
      a.2.sourceArc.darts_length]
  by_cases ht : a.2.target = some i
  · have hnodup : (targetDarts Delta a.2.target).Nodup := by
      rw [ht]
      exact cellDarts_nodup Delta i
    have htlen : a.2.targetArc.darts.toFinset.card = a.2.targetArc.length := by
      rw [List.toFinset_card_of_nodup (a.2.targetArc.darts_nodup hnodup),
        a.2.targetArc.darts_length]
    have hdisj : Disjoint a.2.sourceArc.darts.toFinset a.2.targetArc.darts.toFinset := by
      apply Finset.disjoint_left.mpr
      intro d hs hd
      exact a.2.source_target_darts_disjoint i ht (List.mem_toFinset.mp hs)
        (List.mem_toFinset.mp hd)
    by_cases hs : a.2.source = i
    · simp only [cellArcDarts, hs, ht, if_true, Finset.card_union_of_disjoint hdisj, hslen, htlen]
    · simp only [cellArcDarts, hs, ht, if_false, if_true, Finset.empty_union, htlen, Nat.zero_add]
  · by_cases hs : a.2.source = i
    · simp only [cellArcDarts, hs, ht, if_true, if_false, Finset.union_empty, hslen, Nat.add_zero]
    · simp only [cellArcDarts, hs, ht, if_false, Finset.union_empty, Finset.card_empty, Nat.add_zero]

/-- A cell-to-cell region contributes both lengths over all relator cells. -/
theorem sum_card_cellArcDarts_of_target (a : RegionCandidate D eps Delta)
    (j : Fin Delta.rCellCount) (ht : a.2.target = some j) :
    (∑ i : Fin Delta.rCellCount, (a.cellArcDarts i).card) = a.weight := by
  classical
  simp only [card_cellArcDarts, ht, Option.some.injEq, Finset.sum_add_distrib]
  simp [weight]

/-- A region to the outer boundary contributes only its source length. -/
theorem sum_card_cellArcDarts_of_outer (a : RegionCandidate D eps Delta)
    (ht : a.2.target = none) :
    (∑ i : Fin Delta.rCellCount, (a.cellArcDarts i).card) = a.2.sourceArc.length := by
  classical
  simp [card_cellArcDarts, ht]

/-- `true` selects interior regions; `false` selects exterior regions. -/
noncomputable def ofKind (selected : Finset (RegionCandidate D eps Delta))
    (interior : Bool) : Finset (RegionCandidate D eps Delta) := by
  classical
  exact selected.filter fun a => a.2.target.isSome = interior

/-- Union of the retained cell arcs of the specified kind. -/
noncomputable def boundDarts (selected : Finset (RegionCandidate D eps Delta))
    (interior : Bool) (i : Fin Delta.rCellCount) : Finset Delta.toCombMap.Dart := by
  classical
  exact (ofKind selected interior).biUnion fun a => a.cellArcDarts i

theorem boundDarts_subset (selected : Finset (RegionCandidate D eps Delta))
    (interior : Bool) (i : Fin Delta.rCellCount) :
    boundDarts selected interior i ⊆ (cellDarts Delta i).toFinset := by
  classical
  intro d hd
  obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
  exact a.cellArcDarts_subset i hd

theorem card_boundDarts (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) (interior : Bool)
    (i : Fin Delta.rCellCount) :
    (boundDarts selected interior i).card =
      ∑ a ∈ ofKind selected interior, (a.cellArcDarts i).card := by
  classical
  apply Finset.card_biUnion
  intro a ha b hb hab
  exact cellArcDarts_disjoint
    (hpairwise a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab) i

theorem boundDarts_disjoint (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) (i : Fin Delta.rCellCount) :
    Disjoint (boundDarts selected false i) (boundDarts selected true i) := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hd he
  obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨b, hb, he⟩ := Finset.mem_biUnion.mp he
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hab : a ≠ b := by
    intro hab
    subst b
    rw [ha'.2] at hb'
    simp at hb'
  exact Finset.disjoint_left.mp
    (cellArcDarts_disjoint (hpairwise a ha'.1 b hb'.1 hab) i) hd he

/-- A dart is unbound precisely when no retained region uses it at this cell. -/
noncomputable def unboundDarts (selected : Finset (RegionCandidate D eps Delta))
    (i : Fin Delta.rCellCount) : Finset Delta.toCombMap.Dart := by
  classical
  exact (cellDarts Delta i).toFinset \
    (boundDarts selected false i ∪ boundDarts selected true i)

/-- The actual cell perimeter is partitioned exactly into the three counts. -/
theorem perimeter_eq (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) (i : Fin Delta.rCellCount) :
    (cell Delta i).word.length =
      (boundDarts selected false i).card + (boundDarts selected true i).card +
        (unboundDarts selected i).card := by
  classical
  have hsub : boundDarts selected false i ∪ boundDarts selected true i ⊆
      (cellDarts Delta i).toFinset :=
    Finset.union_subset (boundDarts_subset selected false i)
      (boundDarts_subset selected true i)
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_union_of_disjoint (boundDarts_disjoint selected hpairwise i),
    List.toFinset_card_of_nodup (cellDarts_nodup Delta i),
    CellBoundaryPartition.cellDarts_length_eq_word_length Delta i] at hc
  change _ = _ + _ + ((cellDarts Delta i).toFinset \ _).card
  omega

/-- The total interior count is exactly the sum of the selected interior
regions' actual optimization weights. -/
theorem sum_interior_card (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) :
    (∑ i : Fin Delta.rCellCount, (boundDarts selected true i).card) =
      ∑ a ∈ ofKind selected true, a.weight := by
  classical
  simp only [card_boundDarts selected hpairwise]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have ht : a.2.target.isSome = true := (Finset.mem_filter.mp ha).2
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp ht
  exact a.sum_card_cellArcDarts_of_target j hj

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.card_cellArcDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.perimeter_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.sum_interior_card
