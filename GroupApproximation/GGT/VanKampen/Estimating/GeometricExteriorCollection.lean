import GroupApproximation.GGT.VanKampen.Estimating.GeometricGreendlinger
import GroupApproximation.GGT.VanKampen.Estimating.UnboundParameters

/-!
# A large collection of exterior arcs before the selected-cell descent

Osin's Appendix Corollary 9.6 first finds a cell with large total exterior
contiguity. Lemma 9.7(b) then minimizes enclosed cell counts to obtain the
single exterior region. This intermediate count requires no global exterior
uniqueness. The stronger square-root threshold is constructed at the same
epsilon, by increasing rho when necessary.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC Embedded
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

namespace Embedded.GeometricCandidate

noncomputable def exteriorAt (selected : Finset (GeometricCandidate D eps Delta))
    (i : Fin Delta.rCellCount) : Finset (GeometricCandidate D eps Delta) :=
  (ofKind selected false).filter fun a => a.2.source = i

/-- The actual exterior dart count is the sum of all retained source arcs
at this cell, even when there are several such regions. -/
theorem card_exterior_sum (selected : Finset (GeometricCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected)
    (i : Fin Delta.rCellCount) :
    (boundDarts selected false i).card = ∑ a ∈ exteriorAt selected i, a.2.sourceArc.length := by
  rw [card_boundDarts selected hpairwise, exteriorAt, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have ht : a.2.target ≠ some i := by
    rw [target_eq_none_of_mem_ofKind_false ha]
    intro h
    cases h
  simp only [card_cellArcDarts, if_neg ht, Nat.add_zero]

theorem exists_large_exterior_collection (selected : Finset (GeometricCandidate D eps Delta))
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

/-- Retain the strict square-root estimate when transferring it to the
one-mu perimeter budget used before the final two-mu loss. -/
theorem unbound_total_lt_mu (selected : Finset (GeometricCandidate D eps Delta))
    {rho : ℕ} {mu : ℝ} (hperimeter : ∀ i : Fin Delta.rCellCount, rho ≤ (cell Delta i).word.length)
    (hmu : 0 ≤ mu)
    (hlemma62 : (∑ i : Fin Delta.rCellCount, ((unboundDarts selected i).card : ℝ)) <
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
      (Delta.rCellCount : ℝ) * (rho : ℝ) = ∑ _i : Fin Delta.rCellCount, (rho : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by exact_mod_cast hperimeter i
  calc
    _ < (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) := hlemma62
    _ ≤ (Delta.rCellCount : ℝ) * (mu * (rho : ℝ)) :=
      mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg _)
    _ = mu * ((Delta.rCellCount : ℝ) * (rho : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hmu

end Embedded.GeometricCandidate

theorem RealizedGeometricFamily.exists_large_exterior_collection
    (S : RealizedGeometricFamily D eps Delta) {rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hmu : 0 ≤ mu)
    (hplanar : HasEndpointClosedPlanarEdgeBound
      (GeometricCandidate.InteriorEdge.Incident (selected := S.family)))
    (hlemma62 : (∑ i : Fin S.diagram.rCellCount,
      ((GeometricCandidate.unboundDarts S.family i).card : ℝ)) <
        (S.diagram.rCellCount : ℝ) * Real.sqrt (rho : ℝ))
    (hthreshold : 1 ≤ mu * Real.sqrt (rho : ℝ)) :
    ∃ i : Fin S.diagram.rCellCount,
      (1 - 11 * mu) * ((cell S.diagram i).word.length : ℝ) <
        ∑ a ∈ GeometricCandidate.exteriorAt S.family i, (a.2.sourceArc.length : ℝ) := by
  apply GeometricCandidate.exists_large_exterior_collection S.family S.pairwise
  · exact GeometricCandidate.interior_total_le S.family S.pairwise hplanar S.reduced hcondition hmu
  · exact GeometricCandidate.unbound_total_lt_mu S.family
      (fun i => hcondition.long _ (cell S.diagram i).word_mem) hmu hlemma62 hthreshold

namespace UnboundEstimate

/-- Produce the stronger numerical threshold together with every existing
scale inequality, at a fixed epsilon. The relator condition's mu is unchanged. -/
theorem exists_osinUnboundScale_one_mu_after_epsilon
    (lambda c mu kappa c1 c2 : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu)
    (eps : ℕ) (heps : c1 + 2 * kappa < (eps : ℝ)) :
    ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
      OsinUnboundScale lambda c mu kappa c1 c2 eps rho ∧
        1 ≤ mu * Real.sqrt (rho : ℝ) := by
  obtain ⟨rho0, hrho0, hscale⟩ := exists_osinUnboundScale_after_epsilon
    lambda c (mu / 2) kappa c1 c2 hlambda (div_pos hmu (by norm_num)) eps heps
  refine ⟨rho0, hrho0, ?_⟩
  intro rho hrho
  have S := hscale rho hrho
  have hone : 1 ≤ mu * Real.sqrt (rho : ℝ) := by
    have h := S.threshold
    linarith
  refine ⟨{
    epsilon_large := S.epsilon_large
    rho_pos := S.rho_pos
    density_large := S.density_large
    shortcut_shortens := S.shortcut_shortens
    threshold := by linarith }, hone⟩

end UnboundEstimate
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.card_exterior_sum
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.exists_large_exterior_collection
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedGeometricFamily.exists_large_exterior_collection
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_osinUnboundScale_one_mu_after_epsilon
