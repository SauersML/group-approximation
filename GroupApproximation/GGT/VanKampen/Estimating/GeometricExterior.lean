import GroupApproximation.GGT.VanKampen.Estimating.GeometricPartition

/-!
# Extracting a large exterior arc from the retained boundary counts

Exterior uniqueness identifies the exterior dart count at a cell with one
actual selected witness. The two global budgets then give the strict source
Greendlinger conclusion. No face-only candidate or chosen replacement witness
occurs in this count. Exterior uniqueness and the budgets remain explicit
geometric inputs until their producers are constructed.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

open scoped Classical

theorem target_eq_none_of_mem_ofKind_false
    {selected : Finset (GeometricCandidate D eps Delta)}
    {a : GeometricCandidate D eps Delta} (ha : a ∈ ofKind selected false) :
    a.2.target = none := by
  have ht := (Finset.mem_filter.mp ha).2
  cases heq : a.2.target <;> simp_all

def ExteriorUnique (selected : Finset (GeometricCandidate D eps Delta)) : Prop :=
  ∀ a ∈ ofKind selected false, ∀ b ∈ ofKind selected false,
    a.2.source = b.2.source → a = b

/-- Uniqueness recovers the length of the supplied exterior witness. -/
theorem card_exterior_eq (selected : Finset (GeometricCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected)
    (hunique : ExteriorUnique selected) (a : GeometricCandidate D eps Delta)
    (ha : a ∈ ofKind selected false) :
    (boundDarts selected false a.2.source).card = a.2.sourceArc.length := by
  rw [card_boundDarts selected hpairwise]
  calc
    (∑ b ∈ ofKind selected false, (b.cellArcDarts a.2.source).card) =
        (a.cellArcDarts a.2.source).card := by
      apply Finset.sum_eq_single a
      · intro b hb hba
        have hs : b.2.source ≠ a.2.source := fun hs =>
          hba (hunique b hb a ha hs)
        have ht := target_eq_none_of_mem_ofKind_false hb
        simp [card_cellArcDarts, hs, ht]
      · intro hnot
        exact (hnot ha).elim
    _ = a.2.sourceArc.length := by
      simp [card_cellArcDarts, target_eq_none_of_mem_ofKind_false ha]

/-- A positive exterior count exposes an actual selected region at the cell. -/
theorem exists_outer_of_pos (selected : Finset (GeometricCandidate D eps Delta))
    (i : Fin Delta.rCellCount) (hpos : 0 < (boundDarts selected false i).card) :
    ∃ a ∈ ofKind selected false, a.2.source = i := by
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
  obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
  refine ⟨a, ha, ?_⟩
  by_contra hs
  have ht := target_eq_none_of_mem_ofKind_false ha
  simp [cellArcDarts, hs, ht] at hd

/-- Summing the literal cell partitions gives the total perimeter identity. -/
theorem total_perimeter_eq (selected : Finset (GeometricCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) :
    (∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ)) =
      (∑ i : Fin Delta.rCellCount, ((boundDarts selected false i).card : ℝ)) +
      (∑ i : Fin Delta.rCellCount, ((boundDarts selected true i).card : ℝ)) +
      (∑ i : Fin Delta.rCellCount, ((unboundDarts selected i).card : ℝ)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact_mod_cast perimeter_eq selected hpairwise i

/-- The two Osin budgets and exterior uniqueness yield one retained exterior
region of degree strictly greater than `1 - 13 * mu`. -/
theorem exists_large_exterior (selected : Finset (GeometricCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected)
    (hunique : ExteriorUnique selected) {mu : ℝ} (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16)
    (hpositive : 0 < ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ))
    (hinterior : (∑ i : Fin Delta.rCellCount, ((boundDarts selected true i).card : ℝ)) ≤
      10 * mu * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ))
    (hunbound : (∑ i : Fin Delta.rCellCount, ((unboundDarts selected i).card : ℝ)) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ)) :
    ∃ a ∈ selected, a.2.target = none ∧
      (1 - 13 * mu) * ((cell Delta a.2.source).word.length : ℝ) <
        (a.2.sourceArc.length : ℝ) := by
  have hpartition := total_perimeter_eq selected hpairwise
  have hslack := mul_pos hmu hpositive
  have htotal : (1 - 13 * mu) *
      (∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ)) <
        ∑ i : Fin Delta.rCellCount, ((boundDarts selected false i).card : ℝ) := by
    linarith
  have hindex : ∃ i : Fin Delta.rCellCount,
      (1 - 13 * mu) * ((cell Delta i).word.length : ℝ) <
        ((boundDarts selected false i).card : ℝ) := by
    by_contra hnone
    have hall : ∀ i : Fin Delta.rCellCount,
        ((boundDarts selected false i).card : ℝ) ≤
          (1 - 13 * mu) * ((cell Delta i).word.length : ℝ) := by
      intro i
      exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hall i
    rw [← Finset.mul_sum] at hsum
    linarith
  obtain ⟨i, hi⟩ := hindex
  have hcoefficient : 0 ≤ 1 - 13 * mu := by linarith
  have hnonneg := mul_nonneg hcoefficient (Nat.cast_nonneg (cell Delta i).word.length)
  have hpos : 0 < (boundDarts selected false i).card := by exact_mod_cast lt_of_le_of_lt hnonneg hi
  obtain ⟨a, ha, hs⟩ := exists_outer_of_pos selected i hpos
  refine ⟨a, (Finset.mem_filter.mp ha).1, target_eq_none_of_mem_ofKind_false ha, ?_⟩
  rw [← hs, card_exterior_eq selected hpairwise hunique a ha] at hi
  exact hi

end GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.card_exterior_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.exists_large_exterior
