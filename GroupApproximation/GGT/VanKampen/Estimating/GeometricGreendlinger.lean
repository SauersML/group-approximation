import GroupApproximation.GGT.VanKampen.Estimating.GeometricExterior
import GroupApproximation.GGT.VanKampen.Estimating.GeometricIncidence
import GroupApproximation.GGT.VanKampen.Estimating.GeometricGlobalSelection

/-!
# Greendlinger counting for the actual global geometric selection

The constructed selection retains all contiguity data, even across changes
of diagram. This module combines its literal dart counts and O52 charges
with the planar, exterior-uniqueness and unbound outputs still needed from
the geometric argument. It returns the original strict exterior-arc
conclusion without constructing the historical face-only estimating system.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

open Embedded
open scoped Classical

/-- The strict Lemma 62 dart bound implies the required uncovered budget
at the same epsilon and rho. -/
theorem Embedded.GeometricCandidate.unbound_total_le_two_mu
    (selected : Finset (GeometricCandidate D eps Delta)) {rho : ℕ} {mu : ℝ}
    (hperimeter : ∀ i : Fin Delta.rCellCount, rho ≤ (cell Delta i).word.length)
    (hmu : 0 ≤ mu)
    (hlemma62 : (∑ i : Fin Delta.rCellCount,
      ((GeometricCandidate.unboundDarts selected i).card : ℝ)) <
        (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ))
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    (∑ i : Fin Delta.rCellCount, ((GeometricCandidate.unboundDarts selected i).card : ℝ)) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ) := by
  have hscale : Real.sqrt (rho : ℝ) ≤ 2 * mu * (rho : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hthreshold (Real.sqrt_nonneg (rho : ℝ))
    rwa [one_mul, mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg rho)] at h
  have hp : (Delta.rCellCount : ℝ) * (rho : ℝ) ≤
      ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ) := by
    calc
      (Delta.rCellCount : ℝ) * (rho : ℝ) = ∑ _i : Fin Delta.rCellCount, (rho : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by exact_mod_cast hperimeter i
  calc
    (∑ i : Fin Delta.rCellCount, ((GeometricCandidate.unboundDarts selected i).card : ℝ)) ≤
        (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) := le_of_lt hlemma62
    _ ≤ (Delta.rCellCount : ℝ) * (2 * mu * (rho : ℝ)) :=
      mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg _)
    _ = 2 * mu * ((Delta.rCellCount : ℝ) * (rho : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) hmu)

/-- Once the geometric producer supplies its three missing conclusions on
the attained global optimum, all remaining Greendlinger counting is proved.
The O52 equations are derived from this optimum's own reduced diagram. -/
theorem GloballyDistinguishedGeometricFamily.exists_large_exterior
    (S : GloballyDistinguishedGeometricFamily D eps Delta)
    {rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hrho : 0 < rho) (hcells : 0 < Delta.rCellCount)
    (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16)
    (hplanar : HasEndpointClosedPlanarEdgeBound
      (GeometricCandidate.InteriorEdge.Incident (selected := S.family)))
    (hunique : GeometricCandidate.ExteriorUnique S.family)
    (hlemma62 : (∑ i : Fin S.diagram.rCellCount,
      ((GeometricCandidate.unboundDarts S.family i).card : ℝ)) <
        (S.diagram.rCellCount : ℝ) * Real.sqrt (rho : ℝ))
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    ∃ (faces : Finset S.diagram.toCombMap.Face) (Gamma : Contiguity D eps S.diagram faces),
      Gamma.target = none ∧
        (1 - 13 * mu) * ((cell S.diagram Gamma.source).word.length : ℝ) <
          (Gamma.sourceArc.length : ℝ) := by
  have hinterior := GeometricCandidate.interior_total_le S.family S.pairwise
    hplanar S.reduced hcondition (le_of_lt hmu)
  have hperimeter (i : Fin S.diagram.rCellCount) : rho ≤ (cell S.diagram i).word.length :=
    hcondition.long _ (cell S.diagram i).word_mem
  have hunbound := GeometricCandidate.unbound_total_le_two_mu S.family
    hperimeter (le_of_lt hmu) hlemma62 hthreshold
  have hpositive : 0 < ∑ i : Fin S.diagram.rCellCount, ((cell S.diagram i).word.length : ℝ) := by
    apply Finset.sum_pos
    · intro i _
      have h := lt_of_lt_of_le hrho (hperimeter i)
      exact_mod_cast h
    · apply Finset.univ_nonempty_iff.mpr
      apply Fin.pos_iff_nonempty.mp
      rwa [S.equiv.rCellCount_eq]
  obtain ⟨a, _ha, ht, hlarge⟩ := GeometricCandidate.exists_large_exterior S.family
    S.pairwise hunique hmu hmuUpper hpositive hinterior hunbound
  exact ⟨a.1, a.2, ht, hlarge⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.unbound_total_le_two_mu
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedGeometricFamily.exists_large_exterior
