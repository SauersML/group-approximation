import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.CandidateParts.Signs
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Finset.Max

/-!
# Candidate points for realizable sign vectors

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof: "Fixed-dimensional
feasibility is decidable over the real closed field."  In the univariate step of
Tarski's decision procedure, a sign vector of a finite list `ps` of nonzero real
polynomials is realized somewhere on `ℝ` iff it is realized at a root of `∏ ps`,
at a root of `(∏ ps)'`, or at `±∞` (Basu--Pollack--Roy, *Algorithms in Real
Algebraic Geometry*, §2.3, Prop. 2.37; Hörmander's proof of Tarski--Seidenberg).

Main result: `exists_sgnVec_iff`.

Proof of `→`: at a point `x0` with `(∏ ps)(x0) ≠ 0`, if `∏ ps` has no root above
(below) `x0`, the intermediate value theorem shows the signs at `x0` are the
signs at `+∞` (`-∞`); otherwise take the nearest roots `a < x0 < b`; Rolle's
theorem gives a root `c ∈ (a, b)` of `(∏ ps)'` (which is nonzero, since `∏ ps`
is a nonzero polynomial with a root), and the signs at `c` and `x0` agree.
The statement holds for `ps = []` as well (both sides are then true exactly
for `σ = []`).
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

/-- Rolle step: between two roots of `∏ ps` enclosing `x0`, there is a root of
`(∏ ps)'` with the same sign vector as `x0`. -/
theorem cand_rolle (ps : List ℝ[X]) (hf0 : ps.prod ≠ 0) (x0 : ℝ)
    (hx0 : ps.prod.eval x0 ≠ 0) (habove : ∃ b, x0 < b ∧ ps.prod.eval b = 0)
    (hbelow : ∃ a, a < x0 ∧ ps.prod.eval a = 0) :
    ∃ x ∈ (derivative ps.prod).roots, sgnVec ps x = sgnVec ps x0 := by
  obtain ⟨a0, ha0x, ha0⟩ := hbelow
  obtain ⟨b0, hb0x, hb0⟩ := habove
  have hmem : ∀ r : ℝ, ps.prod.eval r = 0 → r ∈ ps.prod.roots.toFinset := fun r hr =>
    Multiset.mem_toFinset.mpr ((mem_roots hf0).mpr hr)
  have hroot : ∀ r ∈ ps.prod.roots.toFinset, ps.prod.eval r = 0 := fun r hr =>
    (mem_roots hf0).mp (Multiset.mem_toFinset.mp hr)
  have hA : (ps.prod.roots.toFinset.filter (fun r => r < x0)).Nonempty :=
    ⟨a0, Finset.mem_filter.mpr ⟨hmem a0 ha0, ha0x⟩⟩
  have hB : (ps.prod.roots.toFinset.filter (fun r => x0 < r)).Nonempty :=
    ⟨b0, Finset.mem_filter.mpr ⟨hmem b0 hb0, hb0x⟩⟩
  obtain ⟨a, haA, ha_max⟩ : ∃ a ∈ ps.prod.roots.toFinset.filter (fun r => r < x0),
      ∀ r ∈ ps.prod.roots.toFinset.filter (fun r => r < x0), r ≤ a :=
    ⟨_, Finset.max'_mem _ hA, fun r hr => Finset.le_max' _ r hr⟩
  obtain ⟨b, hbB, hb_min⟩ : ∃ b ∈ ps.prod.roots.toFinset.filter (fun r => x0 < r),
      ∀ r ∈ ps.prod.roots.toFinset.filter (fun r => x0 < r), b ≤ r :=
    ⟨_, Finset.min'_mem _ hB, fun r hr => Finset.min'_le _ r hr⟩
  have hax : a < x0 := (Finset.mem_filter.mp haA).2
  have hbx : x0 < b := (Finset.mem_filter.mp hbB).2
  have hfa : ps.prod.eval a = 0 := hroot a (Finset.mem_filter.mp haA).1
  have hfb : ps.prod.eval b = 0 := hroot b (Finset.mem_filter.mp hbB).1
  have hgap : ∀ z ∈ Set.Ioo a b, ps.prod.eval z ≠ 0 := by
    intro z hz h0
    rcases lt_trichotomy z x0 with hzx | hzx | hzx
    · have hzA : z ∈ ps.prod.roots.toFinset.filter (fun r => r < x0) :=
        Finset.mem_filter.mpr ⟨hmem z h0, hzx⟩
      exact absurd (ha_max z hzA) (not_le.mpr hz.1)
    · rw [hzx] at h0
      exact hx0 h0
    · have hzB : z ∈ ps.prod.roots.toFinset.filter (fun r => x0 < r) :=
        Finset.mem_filter.mpr ⟨hmem z h0, hzx⟩
      exact absurd (hb_min z hzB) (not_le.mpr hz.2)
  have hab : a < b := lt_trans hax hbx
  have hcont : ContinuousOn (fun x => ps.prod.eval x) (Set.Icc a b) :=
    ps.prod.continuous.continuousOn
  have hends : (fun x => ps.prod.eval x) a = (fun x => ps.prod.eval x) b := by
    show ps.prod.eval a = ps.prod.eval b
    rw [hfa, hfb]
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero hab hcont hends
  rw [Polynomial.deriv] at hdc
  have hd0 : derivative ps.prod ≠ 0 := by
    intro hd
    have hC : ps.prod = C (ps.prod.coeff 0) := eq_C_of_derivative_eq_zero hd
    have hco : ps.prod.coeff 0 = 0 := by
      have h := hfa
      rw [hC, eval_C] at h
      exact h
    apply hf0
    rw [hC, hco, C_0]
  refine ⟨c, (mem_roots hd0).mpr hdc, ?_⟩
  rcases le_total c x0 with hcx | hcx
  · exact cand_sgnVec_eq_of_Icc ps hcx fun z hz =>
      hgap z ⟨lt_of_lt_of_le hc.1 hz.1, lt_of_le_of_lt hz.2 hbx⟩
  · exact (cand_sgnVec_eq_of_Icc ps hcx fun z hz =>
      hgap z ⟨lt_of_lt_of_le hax hz.1, lt_of_le_of_lt hz.2 hc.2⟩).symm

/-- Forward direction of `exists_sgnVec_iff`, for the sign vector at a given point. -/
theorem cand_forward (ps : List ℝ[X]) (hps : ∀ p ∈ ps, p ≠ 0) (x0 : ℝ) :
    (∃ x ∈ ps.prod.roots, sgnVec ps x = sgnVec ps x0) ∨
      (∃ x ∈ (derivative ps.prod).roots, sgnVec ps x = sgnVec ps x0) ∨
      ps.map sgnTop = sgnVec ps x0 ∨ ps.map sgnBot = sgnVec ps x0 := by
  have hf0 : ps.prod ≠ 0 := List.prod_ne_zero fun h => hps 0 h rfl
  by_cases hx0 : ps.prod.eval x0 = 0
  · exact Or.inl ⟨x0, (mem_roots hf0).mpr hx0, rfl⟩
  by_cases habove : ∃ b, x0 < b ∧ ps.prod.eval b = 0
  · by_cases hbelow : ∃ a, a < x0 ∧ ps.prod.eval a = 0
    · exact Or.inr (Or.inl (cand_rolle ps hf0 x0 hx0 habove hbelow))
    · refine Or.inr (Or.inr (Or.inr ?_))
      obtain ⟨y, hy, hyx⟩ :=
        ((cand_eventually_sgnVec_bot ps hps).and (Filter.eventually_le_atBot x0)).exists
      rw [← hy]
      apply cand_sgnVec_eq_of_Icc ps hyx
      intro z hz h0
      rcases eq_or_lt_of_le hz.2 with hz' | hz'
      · rw [hz'] at h0
        exact hx0 h0
      · exact hbelow ⟨z, hz', h0⟩
  · refine Or.inr (Or.inr (Or.inl ?_))
    obtain ⟨y, hy, hyx⟩ :=
      ((cand_eventually_sgnVec_top ps hps).and (Filter.eventually_ge_atTop x0)).exists
    rw [← hy]
    symm
    apply cand_sgnVec_eq_of_Icc ps hyx
    intro z hz h0
    rcases eq_or_lt_of_le hz.1 with hz' | hz'
    · rw [← hz'] at h0
      exact hx0 h0
    · exact habove ⟨z, hz', h0⟩

open Polynomial in
/-- **Candidate points** (BPR Prop. 2.37): a sign vector of a list of nonzero real
polynomials is realized on `ℝ` iff it is realized at a root of `∏ ps`, at a root of
`(∏ ps)'`, or at `+∞` / `-∞`.  Used in the univariate elimination step of the proof of
`thm:mf-arithmetic` (`non_mf_group_notes.tex`). -/
theorem exists_sgnVec_iff (ps : List ℝ[X]) (hps : ∀ p ∈ ps, p ≠ 0) (σ : List ℤ) :
    (∃ x : ℝ, sgnVec ps x = σ) ↔
      (∃ x ∈ ps.prod.roots, sgnVec ps x = σ) ∨
      (∃ x ∈ (derivative ps.prod).roots, sgnVec ps x = σ) ∨
      ps.map sgnTop = σ ∨ ps.map sgnBot = σ := by
  constructor
  · rintro ⟨x0, hx0⟩
    subst hx0
    exact cand_forward ps hps x0
  · rintro (⟨x, -, hx⟩ | ⟨x, -, hx⟩ | htop | hbot)
    · exact ⟨x, hx⟩
    · exact ⟨x, hx⟩
    · obtain ⟨x, hx⟩ := (cand_eventually_sgnVec_top ps hps).exists
      exact ⟨x, hx.trans htop⟩
    · obtain ⟨x, hx⟩ := (cand_eventually_sgnVec_bot ps hps).exists
      exact ⟨x, hx.trans hbot⟩

end GroupApproximation.Full.NN11b
