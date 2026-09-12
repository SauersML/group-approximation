import GroupApproximation.GGT.DGOProposition414UniformGeneral
import GroupApproximation.Meta.AxiomGuard

/-!
# The arithmetic quasi-geodesic comparison fails for multiplicative error

A fixed additive constant cannot turn the lower bound `t / mu - c` into
`t - b` for arbitrary lengths when `mu > 1`. The original comparison and its
conditional radius bridge are retained; this module proves their premise
impossible at the parameters required by DGO Lemma 4.21.
-/

namespace GroupApproximation.GGT.DGOProposition414.General

/-- The exact `(4,1)` parameter needed in Lemma 4.21 admits no natural
additive comparison constant. -/
theorem not_exists_quasiGeodesicComparison_four_one :
    ¬ ∃ b : ℕ, QuasiGeodesicComparison 4 1 (b : ℝ) := by
  rintro ⟨b, h⟩
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hh := h (by norm_num) (by norm_num) (4 * ((b : ℝ) + 2)) ((b : ℝ) + 1)
    (by positivity) (by positivity) (by linarith)
  linarith

/-- The obstruction holds for every multiplicative constant greater than one
and every finite additive constant, not only the numerical `(4,1)` instance. -/
theorem not_quasiGeodesicComparison_of_one_lt
    {mu c b : ℝ} (hmu : 1 < mu) (hc : 0 ≤ c) :
    ¬ QuasiGeodesicComparison mu c b := by
  intro h
  let d : ℝ := (max b 0 + 1) / (mu - 1)
  have hden : 0 < mu - 1 := by linarith
  have hmu0 : 0 < mu := by linarith
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hmul : (mu - 1) * d = max b 0 + 1 := by
    dsimp [d]
    field_simp
  have hinput : (mu * d) / mu - c ≤ d := by
    rw [mul_div_cancel_left₀ d (ne_of_gt hmu0)]
    linarith
  have hh := h (le_of_lt hmu) hc (mu * d) d (mul_nonneg (le_of_lt hmu0) hd) hd hinput
  have hb : b ≤ max b 0 := le_max_left _ _
  nlinarith


/-- In the source's parameter range, the proposed comparison holds exactly
when there is no multiplicative error and the additive error is absorbed. -/
theorem quasiGeodesicComparison_iff_of_parameters
    {mu c b : ℝ} (hmu : 1 ≤ mu) (hc : 0 ≤ c) :
    QuasiGeodesicComparison mu c b ↔ mu = 1 ∧ c ≤ b := by
  constructor
  · intro h
    have hmuOne : mu = 1 := by
      by_contra hne
      exact not_quasiGeodesicComparison_of_one_lt (lt_of_le_of_ne hmu (Ne.symm hne)) hc h
    subst mu
    have hh := h le_rfl hc c 0 hc le_rfl (by simp)
    norm_num at hh
    exact ⟨rfl, by linarith⟩
  · rintro ⟨rfl, hcb⟩
    exact quasiGeodesicComparison_of_one hc hcb

end GroupApproximation.GGT.DGOProposition414.General

#audit_closed_axioms GroupApproximation.GGT.DGOProposition414.General.not_exists_quasiGeodesicComparison_four_one
#audit_axioms GroupApproximation.GGT.DGOProposition414.General.not_quasiGeodesicComparison_of_one_lt

#audit_axioms GroupApproximation.GGT.DGOProposition414.General.quasiGeodesicComparison_iff_of_parameters
