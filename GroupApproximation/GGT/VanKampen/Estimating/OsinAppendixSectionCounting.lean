import GroupApproximation.GGT.VanKampen.Estimating.RegionPartition
import GroupApproximation.GGT.VanKampen.Estimating.UnboundParameters
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.5 and Corollary 9.6 on actual region families

Osin, arXiv:math/0411039v3, Appendix §9.  Lemma 9.5: under `(∗)` the total
length `Σ₀` of the outer arcs exceeds `(1 − 11μ) Σ`, where `Σ` is the total
perimeter of the relator cells.  Corollary 9.6: some cell `Π` has disjoint
contiguity regions to the sections with total degree above `1 − 11μ`.

This file is the counting behind both, on `Embedded.RegionCandidate` families
(retained geometric witnesses, as in the distinguished section systems of
`Estimating/OsinAppendixSections.lean`).  It ports the counting of
`GeometricExterior` and `GeometricExteriorCollection` from the historical
`GeometricCandidate` to `RegionCandidate`.  Both budgets stay explicit
hypotheses: the interior one (`≤ 10μΣ`) is Lemma 9.1 with the O52 charge, the
unbound one (`< μΣ`) is Lemma 9.4 with the threshold on `ρ`.

No exterior uniqueness is used: the exterior dart count at a cell is the sum of
the source arcs of ALL selected exterior regions at that cell
(`card_exterior_sum`), which is what Corollary 9.6 sums.  A region to a section
has target `none`, so the sum ranges over the regions of `Π` to every section.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

open scoped Classical

/-- A member of the exterior kind targets the outer boundary. -/
theorem target_eq_none_of_mem_ofKind_false
    {selected : Finset (RegionCandidate D eps Delta)}
    {a : RegionCandidate D eps Delta} (ha : a ∈ ofKind selected false) :
    a.2.target = none := by
  have ht := (Finset.mem_filter.mp ha).2
  cases heq : a.2.target <;> simp_all

/-- Summing the cell partitions gives the total perimeter identity. -/
theorem total_perimeter_eq (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) :
    (∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ)) =
      (∑ i : Fin Delta.rCellCount, ((boundDarts selected false i).card : ℝ)) +
      (∑ i : Fin Delta.rCellCount, ((boundDarts selected true i).card : ℝ)) +
      (∑ i : Fin Delta.rCellCount, ((unboundDarts selected i).card : ℝ)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact_mod_cast perimeter_eq selected hpairwise i

/-- The selected exterior regions of one cell. -/
noncomputable def exteriorAt (selected : Finset (RegionCandidate D eps Delta))
    (i : Fin Delta.rCellCount) : Finset (RegionCandidate D eps Delta) :=
  (ofKind selected false).filter fun a => a.2.source = i

/-- **The exterior dart count at a cell is the sum of all its exterior source
arcs**, however many selected exterior regions the cell has. -/
theorem card_exterior_sum (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected)
    (i : Fin Delta.rCellCount) :
    (boundDarts selected false i).card =
      ∑ a ∈ exteriorAt selected i, a.2.sourceArc.length := by
  rw [card_boundDarts selected hpairwise, exteriorAt, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have ht : a.2.target ≠ some i := by
    rw [target_eq_none_of_mem_ofKind_false ha]
    intro h
    cases h
  simp only [card_cellArcDarts, if_neg ht, Nat.add_zero]

/-- **Corollary 9.6, counting half.**  The interior budget `≤ 10μΣ` and the
unbound budget `< μΣ` leave some cell whose selected exterior regions have total
source length above `(1 − 11μ)` times its perimeter. -/
theorem exists_large_exterior_collection
    (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) {mu : ℝ}
    (hinterior : (∑ i : Fin Delta.rCellCount, ((boundDarts selected true i).card : ℝ)) ≤
      10 * mu * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ))
    (hunbound : (∑ i : Fin Delta.rCellCount, ((unboundDarts selected i).card : ℝ)) <
      mu * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ)) :
    ∃ i : Fin Delta.rCellCount,
      (1 - 11 * mu) * ((cell Delta i).word.length : ℝ) <
        ∑ a ∈ exteriorAt selected i, (a.2.sourceArc.length : ℝ) := by
  have hpartition := total_perimeter_eq selected hpairwise
  have htotal : (1 - 11 * mu) *
      (∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ)) <
        ∑ i : Fin Delta.rCellCount, ((boundDarts selected false i).card : ℝ) := by
    linarith
  by_contra hnone
  have hall (i : Fin Delta.rCellCount) : ((boundDarts selected false i).card : ℝ) ≤
      (1 - 11 * mu) * ((cell Delta i).word.length : ℝ) := by
    rw [card_exterior_sum selected hpairwise i, Nat.cast_sum]
    exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hall i
  rw [← Finset.mul_sum] at hsum
  exact (not_lt_of_ge hsum) htotal

/-- **Lemma 9.5's unbound half.**  Osin's `S < n √ρ` with `1 ≤ μ √ρ` and every
relator of length at least `ρ` gives `S < μ Σ`. -/
theorem unbound_total_lt_mu (selected : Finset (RegionCandidate D eps Delta))
    {rho : ℕ} {mu : ℝ}
    (hperimeter : ∀ i : Fin Delta.rCellCount, rho ≤ (cell Delta i).word.length)
    (hmu : 0 ≤ mu)
    (hlemma94 : (∑ i : Fin Delta.rCellCount, ((unboundDarts selected i).card : ℝ)) <
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ))
    (hthreshold : 1 ≤ mu * Real.sqrt (rho : ℝ)) :
    (∑ i : Fin Delta.rCellCount, ((unboundDarts selected i).card : ℝ)) <
      mu * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ) := by
  have hscale : Real.sqrt (rho : ℝ) ≤ mu * (rho : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hthreshold (Real.sqrt_nonneg (rho : ℝ))
    rwa [one_mul, mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg rho)] at h
  have hp : (Delta.rCellCount : ℝ) * (rho : ℝ) ≤
      ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ) := by
    calc
      (Delta.rCellCount : ℝ) * (rho : ℝ) =
          ∑ _i : Fin Delta.rCellCount, (rho : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by exact_mod_cast hperimeter i
  calc
    _ < (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) := hlemma94
    _ ≤ (Delta.rCellCount : ℝ) * (mu * (rho : ℝ)) :=
      mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg _)
    _ = mu * ((Delta.rCellCount : ℝ) * (rho : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hmu

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.total_perimeter_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.card_exterior_sum
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_large_exterior_collection
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.unbound_total_lt_mu
