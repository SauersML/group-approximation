import GroupApproximation.GGT.VanKampen.ExteriorArcCounterexample

/-!
# A face-set candidate does not determine its contiguity-arc weight

In the checked six-dart diagram, the same G-cell digon admits weights two
and zero at epsilon two. The candidate subtype identifies the two witnesses
by proof irrelevance, so its arbitrary chosen weight cannot recover both.
-/

namespace GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample

open Embedded ExteriorArcCounterexample GroupApproximation.WordMetric

noncomputable def high : Contiguity D 2 diagram faces where
  boundary := region.boundary
  source := region.source
  target := region.target
  sourceArc := region.sourceArc
  targetArc := region.targetArc
  rightSide := region.rightSide
  leftSide := region.leftSide
  boundary_decomposition := region.boundary_decomposition
  rightSide_length_le := region.rightSide_length_le.trans (by decide)
  leftSide_length_le := region.leftSide_length_le.trans (by decide)
  rightSide_norm_le := region.rightSide_norm_le.trans (by decide)
  leftSide_norm_le := region.leftSide_norm_le.trans (by decide)
  target_ne_source := region.target_ne_source
  o52Certificate := region.o52Certificate
  pasting := region.pasting

noncomputable def low : Contiguity D 2 diagram faces where
  boundary := regionBoundary
  source := 0
  target := none
  sourceArc := ⟨⟨0, Nat.zero_lt_succ _⟩, 0, Nat.zero_le _⟩
  targetArc := ⟨⟨0, Nat.zero_lt_succ _⟩, 0, Nat.zero_le _⟩
  rightSide := [3, 4]
  leftSide := []
  boundary_decomposition := rfl
  rightSide_length_le := le_rfl
  leftSide_length_le := by decide
  rightSide_norm_le := by
    change wordNorm D.alphabet.carrier (a⁻¹ * (a * 1)) ≤ 2
    simp only [inv_mul_cancel_left, wordNorm_one]
    decide
  leftSide_norm_le := by
    change wordNorm D.alphabet.carrier 1 ≤ 2
    rw [wordNorm_one]
    decide
  target_ne_source := by intro i h; cases h
  o52Certificate := by intro i h; cases h
  pasting := region.pasting

def highCandidate : Candidate D 2 diagram := ⟨faces, ⟨high⟩⟩
def lowCandidate : Candidate D 2 diagram := ⟨faces, ⟨low⟩⟩

theorem same_candidate : highCandidate = lowCandidate := rfl

theorem distinct_weights :
    high.sourceArc.length + high.targetArc.length ≠ low.sourceArc.length + low.targetArc.length := by
  decide

/-- The historical chosen weight cannot equal every realizable witness's weight. -/
theorem not_witness_weight :
    ¬ ∀ H : Contiguity D 2 diagram faces,
      Candidate.weight (⟨faces, ⟨H⟩⟩ : Candidate D 2 diagram) =
        H.sourceArc.length + H.targetArc.length := by
  intro h
  have hh : highCandidate.weight = 2 := h high
  have hl : highCandidate.weight = 0 := h low
  omega

end GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample

#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample.same_candidate
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample.distinct_weights
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample.not_witness_weight
