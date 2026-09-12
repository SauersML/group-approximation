import GroupApproximation.GGT.VanKampen.Estimating.Unbound
import GroupApproximation.Meta.AxiomGuard

/-!
# Strict density in a complementary component

The margin `53 < 60` gives a component strictly above its density threshold,
even when the total unbound length only meets its threshold. This supplies
the strict hypothesis needed by the geodesic replacement polygon argument
in Osin's Appendix Lemma 9.4. The earlier non-strict estimates remain valid.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- The strict margin in the total arc count makes non-strict component
bounds sufficient for a strict total bound. Empty component families are
included without an extra nonemptiness hypothesis. -/
theorem total_lt_of_component_le_sixty
    {d : ℕ} (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (arcCount : Fin d → ℕ) (unboundLength : Fin d → ℝ)
    (hcount : (∑ i : Fin d, arcCount i) ≤ 53 * n)
    (hcomponent : ∀ i : Fin d,
      unboundLength i ≤ (arcCount i : ℝ) * t / 60) :
    (∑ i : Fin d, unboundLength i) < (n : ℝ) * t := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcountReal : (∑ i : Fin d, (arcCount i : ℝ)) ≤ 53 * (n : ℝ) := by
    exact_mod_cast hcount
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcomponent i)
  have hrewrite : (∑ i : Fin d, (arcCount i : ℝ) * t / 60) =
      (∑ i : Fin d, (arcCount i : ℝ)) * (t / 60) := by
    simp_rw [div_eq_mul_inv, mul_assoc]
    rw [Finset.sum_mul]
  rw [hrewrite] at hsum
  have hscaled := mul_le_mul_of_nonneg_right hcountReal (show 0 ≤ t / 60 by positivity)
  have hpositive : 0 < (n : ℝ) * t := mul_pos hnReal ht
  nlinarith

/-- A total at least `n * t` forces a component strictly above `nᵢ * t / 60`.
The strictness is retained when cutting it into a polygon. -/
theorem exists_component_gt_sixty
    {d : ℕ} (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (arcCount : Fin d → ℕ) (unboundLength : Fin d → ℝ)
    (hcount : (∑ i : Fin d, arcCount i) ≤ 53 * n)
    (htotal : (n : ℝ) * t ≤ ∑ i : Fin d, unboundLength i) :
    ∃ i : Fin d, (arcCount i : ℝ) * t / 60 < unboundLength i := by
  by_contra hnone
  push Not at hnone
  exact (not_lt_of_ge htotal)
    (total_lt_of_component_le_sixty n hn t ht arcCount unboundLength hcount hnone)

/-- Cutting into at most four sides per arc preserves strict density. -/
theorem component_gt_twoForty
    {arcCount sideCount : ℕ} {unboundLength t : ℝ}
    (ht : 0 ≤ t) (hsides : sideCount ≤ 4 * arcCount)
    (hdense : (arcCount : ℝ) * t / 60 < unboundLength) :
    (sideCount : ℝ) * t / 240 < unboundLength :=
  lt_of_le_of_lt (component_ge_twoForty ht hsides le_rfl) hdense

/-- The actual strict input of the word-polygon theorem follows from the
global unbound-length lower bound and the two finite arc-count bounds. -/
theorem exists_component_gt_twoForty
    {d : ℕ} (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (arcCount sideCount : Fin d → ℕ) (unboundLength : Fin d → ℝ)
    (hcount : (∑ i : Fin d, arcCount i) ≤ 53 * n)
    (hsides : ∀ i, sideCount i ≤ 4 * arcCount i)
    (htotal : (n : ℝ) * t ≤ ∑ i : Fin d, unboundLength i) :
    ∃ i : Fin d, (sideCount i : ℝ) * t / 240 < unboundLength i := by
  obtain ⟨i, hi⟩ := exists_component_gt_sixty n hn t ht arcCount unboundLength hcount htotal
  exact ⟨i, component_gt_twoForty ht.le (hsides i) hi⟩

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.total_lt_of_component_le_sixty
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_component_gt_sixty
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.component_gt_twoForty
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_component_gt_twoForty
