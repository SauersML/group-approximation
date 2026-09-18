import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Univariate.Defs
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Sign constancy and signs at infinity for real polynomials

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof: "Fixed-dimensional
feasibility is decidable over the real closed field."  Ingredients of the
candidate-point lemma (Basu--Pollack--Roy, *Algorithms in Real Algebraic
Geometry*, §2.3, Prop. 2.37; Hörmander's proof of Tarski--Seidenberg):

* `cand_sgn_eval_eq_of_Icc`: a polynomial without roots on `[x, y]` has the
  same sign at `x` and `y` (intermediate value theorem);
* `cand_sgnVec_eq_of_Icc`: the same for a list `ps`, when `∏ ps` has no roots;
* `cand_eventually_sgnVec_top` / `cand_eventually_sgnVec_bot`: for nonzero
  polynomials, `sgnVec ps x` is eventually `ps.map sgnTop` as `x → +∞`, and
  eventually `ps.map sgnBot` as `x → -∞`.
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

theorem cand_sgn_pos {x : ℝ} (h : 0 < x) : sgn x = 1 := by
  unfold sgn
  rw [if_pos h]

theorem cand_sgn_neg {x : ℝ} (h : x < 0) : sgn x = -1 := by
  unfold sgn
  rw [if_neg (not_lt.mpr h.le), if_pos h]

/-- A real polynomial with no root on `[x, y]` has the same sign at `x` and `y`. -/
theorem cand_sgn_eval_eq_of_Icc (p : ℝ[X]) {x y : ℝ} (hxy : x ≤ y)
    (h : ∀ z ∈ Set.Icc x y, p.eval z ≠ 0) : sgn (p.eval x) = sgn (p.eval y) := by
  have hx : p.eval x ≠ 0 := h x ⟨le_rfl, hxy⟩
  have hy : p.eval y ≠ 0 := h y ⟨hxy, le_rfl⟩
  have hc : ContinuousOn (fun z => p.eval z) (Set.Icc x y) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne hx with hx' | hx'
  · rcases lt_or_gt_of_ne hy with hy' | hy'
    · rw [cand_sgn_neg hx', cand_sgn_neg hy']
    · exfalso
      have h0 : (0 : ℝ) ∈ Set.Icc ((fun z => p.eval z) x) ((fun z => p.eval z) y) :=
        ⟨hx'.le, hy'.le⟩
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hxy hc h0
      exact h z hz hz0
  · rcases lt_or_gt_of_ne hy with hy' | hy'
    · exfalso
      have h0 : (0 : ℝ) ∈ Set.Icc ((fun z => p.eval z) y) ((fun z => p.eval z) x) :=
        ⟨hy'.le, hx'.le⟩
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hxy hc h0
      exact h z hz hz0
    · rw [cand_sgn_pos hx', cand_sgn_pos hy']

/-- A member of `ps` does not vanish where `∏ ps` does not vanish. -/
theorem cand_eval_ne_zero_of_mem {ps : List ℝ[X]} {p : ℝ[X]} (hp : p ∈ ps) {z : ℝ}
    (hz : ps.prod.eval z ≠ 0) : p.eval z ≠ 0 := by
  intro h0
  obtain ⟨q, hq⟩ := List.dvd_prod hp
  apply hz
  rw [hq, eval_mul, h0, zero_mul]

/-- If `∏ ps` has no root on `[x, y]`, the sign vectors of `ps` at `x` and `y` agree. -/
theorem cand_sgnVec_eq_of_Icc (ps : List ℝ[X]) {x y : ℝ} (hxy : x ≤ y)
    (h : ∀ z ∈ Set.Icc x y, ps.prod.eval z ≠ 0) : sgnVec ps x = sgnVec ps y := by
  unfold sgnVec
  apply List.map_congr_left
  intro p hp
  exact cand_sgn_eval_eq_of_Icc p hxy fun z hz => cand_eval_ne_zero_of_mem hp (h z hz)

/-- The sign of a nonzero polynomial is eventually its sign at `+∞`. -/
theorem cand_eventually_sgn_top (p : ℝ[X]) (hp : p ≠ 0) :
    ∀ᶠ x in Filter.atTop, sgn (p.eval x) = sgnTop p := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  by_cases hdeg : 0 < p.degree
  · rcases lt_or_gt_of_ne hlc with hneg | hpos
    · have ht := p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg.le
      refine (ht.eventually_lt_atBot 0).mono fun x hx => ?_
      have hx' : p.eval x < 0 := hx
      rw [sgnTop, cand_sgn_neg hneg, cand_sgn_neg hx']
    · have ht := p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hpos.le
      refine (ht.eventually_gt_atTop 0).mono fun x hx => ?_
      have hx' : 0 < p.eval x := hx
      rw [sgnTop, cand_sgn_pos hpos, cand_sgn_pos hx']
  · have hC : p = C (p.coeff 0) := eq_C_of_degree_le_zero (not_lt.mp hdeg)
    refine Filter.Eventually.of_forall fun x => ?_
    rw [hC, eval_C, sgnTop, leadingCoeff_C]

/-- The sign of a nonzero polynomial is eventually its sign at `-∞`. -/
theorem cand_eventually_sgn_bot (p : ℝ[X]) (hp : p ≠ 0) :
    ∀ᶠ x in Filter.atBot, sgn (p.eval x) = sgnBot p := by
  have hlq : (p.comp (-X)).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff :=
    comp_neg_X_leadingCoeff_eq p
  have hq0 : p.comp (-X) ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [hlq]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hp)
  have hneg : Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop :=
    tendsto_neg_atBot_atTop
  refine (hneg.eventually (cand_eventually_sgn_top (p.comp (-X)) hq0)).mono fun x hx => ?_
  have hx' : sgn ((p.comp (-X)).eval (-x)) = sgnTop (p.comp (-X)) := hx
  have hev : (p.comp (-X)).eval (-x) = p.eval x := by
    rw [eval_comp, eval_neg, eval_X, neg_neg]
  rw [sgnTop, hlq, hev] at hx'
  rw [sgnBot, mul_comm p.leadingCoeff]
  exact hx'

/-- For nonzero polynomials, `sgnVec ps x = ps.map sgnTop` for all large `x`. -/
theorem cand_eventually_sgnVec_top (ps : List ℝ[X]) (hps : ∀ p ∈ ps, p ≠ 0) :
    ∀ᶠ x in Filter.atTop, sgnVec ps x = ps.map sgnTop := by
  revert hps
  induction ps with
  | nil => exact fun _ => Filter.Eventually.of_forall fun _ => rfl
  | cons p ps ih =>
    intro hps
    have hp : p ≠ 0 := hps p (List.mem_cons.mpr (Or.inl rfl))
    have ht : ∀ q ∈ ps, q ≠ 0 := fun q hq => hps q (List.mem_cons.mpr (Or.inr hq))
    refine ((cand_eventually_sgn_top p hp).and (ih ht)).mono fun x hx => ?_
    have h1 : sgn (p.eval x) = sgnTop p := hx.1
    have h2 : sgnVec ps x = ps.map sgnTop := hx.2
    show sgn (p.eval x) :: sgnVec ps x = sgnTop p :: ps.map sgnTop
    rw [h1, h2]

/-- For nonzero polynomials, `sgnVec ps x = ps.map sgnBot` for all very negative `x`. -/
theorem cand_eventually_sgnVec_bot (ps : List ℝ[X]) (hps : ∀ p ∈ ps, p ≠ 0) :
    ∀ᶠ x in Filter.atBot, sgnVec ps x = ps.map sgnBot := by
  revert hps
  induction ps with
  | nil => exact fun _ => Filter.Eventually.of_forall fun _ => rfl
  | cons p ps ih =>
    intro hps
    have hp : p ≠ 0 := hps p (List.mem_cons.mpr (Or.inl rfl))
    have ht : ∀ q ∈ ps, q ≠ 0 := fun q hq => hps q (List.mem_cons.mpr (Or.inr hq))
    refine ((cand_eventually_sgn_bot p hp).and (ih ht)).mono fun x hx => ?_
    have h1 : sgn (p.eval x) = sgnBot p := hx.1
    have h2 : sgnVec ps x = ps.map sgnBot := hx.2
    show sgn (p.eval x) :: sgnVec ps x = sgnBot p :: ps.map sgnBot
    rw [h1, h2]

end GroupApproximation.Full.NN11b
