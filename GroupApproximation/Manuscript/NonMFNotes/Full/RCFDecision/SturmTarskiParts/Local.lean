import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Univariate.Defs
import Mathlib.Analysis.Polynomial.Order

/-!
# Sturm--Tarski, part 1: signs and local structure at a point

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  Toward the Sturm--Tarski
theorem (Basu--Pollack--Roy, *Algorithms in Real Algebraic Geometry*, Thm 2.58
via Thm 2.57 and Prop 2.55) we work purely algebraically: at a point `x`, a
nonzero real polynomial is `F = (X - x)^m · G` with `G(x) ≠ 0`; `m` is the root
multiplicity and `lc0 x F = G(x)` is the local leading coefficient.

This file proves the elementary sign calculus (`sgn_mul`, `sgn_pow`), the
uniqueness of this local decomposition (`of_decomp`), its behaviour under
products and positive scaling, the cancellation lemma `mu_lc0_of_dvd_add`, and
the two analytic facts needed later: beyond the largest root a polynomial has
the sign of its leading coefficient, and a root-free polynomial has equal signs
at `±∞`.
-/

namespace GroupApproximation.Full.NN11b

namespace ST

open Polynomial

noncomputable section

theorem sgn_of_pos {a : ℝ} (h : 0 < a) : sgn a = 1 := by
  unfold sgn
  rw [if_pos h]

theorem sgn_of_neg {a : ℝ} (h : a < 0) : sgn a = -1 := by
  unfold sgn
  rw [if_neg (not_lt.mpr h.le), if_pos h]

theorem sgn_zero : sgn 0 = 0 := by
  unfold sgn
  rw [if_neg (lt_irrefl (0 : ℝ)), if_neg (lt_irrefl (0 : ℝ))]

theorem sgn_mul (a b : ℝ) : sgn (a * b) = sgn a * sgn b := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [sgn_of_pos (mul_pos_of_neg_of_neg ha hb), sgn_of_neg ha, sgn_of_neg hb, neg_one_mul,
        neg_neg]
    · rw [hb, mul_zero, sgn_zero, mul_zero]
    · rw [sgn_of_neg (mul_neg_of_neg_of_pos ha hb), sgn_of_neg ha, sgn_of_pos hb, mul_one]
  · rw [ha, zero_mul, sgn_zero, zero_mul]
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [sgn_of_neg (mul_neg_of_pos_of_neg ha hb), sgn_of_pos ha, sgn_of_neg hb, one_mul]
    · rw [hb, mul_zero, sgn_zero, mul_zero]
    · rw [sgn_of_pos (mul_pos ha hb), sgn_of_pos ha, sgn_of_pos hb, mul_one]

theorem sgn_pow (a : ℝ) (n : ℕ) : sgn (a ^ n) = sgn a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, sgn_of_pos one_pos]
  | succ n ih => rw [pow_succ, pow_succ, sgn_mul, ih]

theorem sgn_neg_one_pow_mul (n : ℕ) (a : ℝ) : sgn ((-1) ^ n * a) = (-1) ^ n * sgn a := by
  rw [sgn_mul, sgn_pow, sgn_of_neg (by norm_num : (-1 : ℝ) < 0)]

theorem sgn_cases {a : ℝ} (h : a ≠ 0) : sgn a = 1 ∨ sgn a = -1 := by
  rcases lt_trichotomy a 0 with h1 | h1 | h1
  · exact Or.inr (sgn_of_neg h1)
  · exact absurd h1 h
  · exact Or.inl (sgn_of_pos h1)

/-- The local leading coefficient `G(x)` of `F = (X - x)^m · G`, `m` the root
multiplicity of `F` at `x`. -/
def lc0 (x : ℝ) (F : ℝ[X]) : ℝ := eval x (F /ₘ (X - C x) ^ rootMultiplicity x F)

theorem exists_decomp (x : ℝ) {F : ℝ[X]} (hF : F ≠ 0) :
    ∃ (n : ℕ) (G : ℝ[X]), rootMultiplicity x F = n ∧ F = (X - C x) ^ n * G ∧
      eval x G ≠ 0 ∧ lc0 x F = eval x G :=
  ⟨rootMultiplicity x F, F /ₘ (X - C x) ^ rootMultiplicity x F, rfl,
    (pow_mul_divByMonic_rootMultiplicity_eq F x).symm,
    eval_divByMonic_pow_rootMultiplicity_ne_zero x hF, rfl⟩

theorem lc0_ne_zero (x : ℝ) {F : ℝ[X]} (hF : F ≠ 0) : lc0 x F ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero x hF

/-- Uniqueness of the local decomposition. -/
theorem of_decomp {x : ℝ} {F G : ℝ[X]} {n : ℕ} (h : F = (X - C x) ^ n * G)
    (hG : eval x G ≠ 0) : rootMultiplicity x F = n ∧ lc0 x F = eval x G := by
  have hG0 : G ≠ 0 := by
    intro h0
    apply hG
    rw [h0, eval_zero]
  have hmu : rootMultiplicity x F = n := by
    rw [h, mul_comm, rootMultiplicity_mul_X_sub_C_pow hG0,
      rootMultiplicity_eq_zero (p := G) (x := x) hG, zero_add]
  refine ⟨hmu, ?_⟩
  unfold lc0
  rw [hmu, h, mul_divByMonic_cancel_left G ((monic_X_sub_C x).pow n)]

theorem mu_lc0_C_mul {c : ℝ} (hc : c ≠ 0) (x : ℝ) {F : ℝ[X]} (hF : F ≠ 0) :
    rootMultiplicity x (C c * F) = rootMultiplicity x F ∧ lc0 x (C c * F) = c * lc0 x F := by
  obtain ⟨n, G, hn, hFG, hG, hl⟩ := exists_decomp x hF
  have h2 : C c * F = (X - C x) ^ n * (C c * G) := by
    rw [hFG]
    ring
  have h3 : eval x (C c * G) ≠ 0 := by
    rw [eval_mul, eval_C]
    exact mul_ne_zero hc hG
  obtain ⟨h4, h5⟩ := of_decomp h2 h3
  refine ⟨by rw [h4, hn], ?_⟩
  rw [h5, hl, eval_mul, eval_C]

theorem mu_lc0_mul (x : ℝ) {F H : ℝ[X]} (hF : F ≠ 0) (hH : H ≠ 0) :
    rootMultiplicity x (F * H) = rootMultiplicity x F + rootMultiplicity x H ∧
      lc0 x (F * H) = lc0 x F * lc0 x H := by
  obtain ⟨n, G, hn, hFG, hG, hl⟩ := exists_decomp x hF
  obtain ⟨k, K, hk, hHK, hK, hl'⟩ := exists_decomp x hH
  have h2 : F * H = (X - C x) ^ (n + k) * (G * K) := by
    rw [hFG, hHK]
    ring
  have h3 : eval x (G * K) ≠ 0 := by
    rw [eval_mul]
    exact mul_ne_zero hG hK
  obtain ⟨h4, h5⟩ := of_decomp h2 h3
  exact ⟨by rw [h4, hn, hk], by rw [h5, hl, hl', eval_mul]⟩

/-- If `(X - x)^n ∣ F + G` and `F` vanishes to order `< n` at `x`, then `G` has
the same order at `x` and the opposite local leading coefficient. -/
theorem mu_lc0_of_dvd_add {x : ℝ} {F G : ℝ[X]} (n : ℕ) (hF : F ≠ 0)
    (hlt : rootMultiplicity x F < n) (hdvd : (X - C x) ^ n ∣ F + G) :
    rootMultiplicity x G = rootMultiplicity x F ∧ lc0 x G = -lc0 x F := by
  obtain ⟨m, F0, hm, hFF, hF0, hl⟩ := exists_decomp x hF
  obtain ⟨H, hH⟩ := hdvd
  obtain ⟨j, rfl⟩ : ∃ j, n = m + (j + 1) := ⟨n - m - 1, by omega⟩
  have hG : G = (X - C x) ^ (m + (j + 1)) * H - F := by
    rw [← hH]
    ring
  have h2 : G = (X - C x) ^ m * ((X - C x) ^ (j + 1) * H - F0) := by
    rw [hG, hFF]
    ring
  have h4 : eval x ((X - C x) ^ (j + 1) * H - F0) = -eval x F0 := by
    rw [eval_sub, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow (by omega : j + 1 ≠ 0), zero_mul, zero_sub]
  have h3 : eval x ((X - C x) ^ (j + 1) * H - F0) ≠ 0 := by
    rw [h4, neg_ne_zero]
    exact hF0
  obtain ⟨h5, h6⟩ := of_decomp h2 h3
  exact ⟨by rw [h5, hm], by rw [h6, h4, hl]⟩

/-- Beyond all roots, a nonzero polynomial has the sign of its leading coefficient. -/
theorem sgn_eval_of_roots_lt {G : ℝ[X]} {x : ℝ} (hG : G ≠ 0)
    (hroots : ∀ y, G.IsRoot y → y < x) : sgn (G.eval x) = sgn G.leadingCoeff := by
  rcases lt_trichotomy G.leadingCoeff 0 with h | h | h
  · rw [sgn_of_neg h, sgn_of_neg (eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hroots h.le)]
  · exact absurd (leadingCoeff_eq_zero.mp h) hG
  · rw [sgn_of_pos h, sgn_of_pos (zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroots h.le)]

/-- A nonzero polynomial without real roots has the same sign at `+∞` and `-∞`. -/
theorem sgnTop_eq_sgnBot_of_no_roots {F : ℝ[X]} (hF : F ≠ 0) (hroots : ∀ y, ¬F.IsRoot y) :
    sgnTop F = sgnBot F := by
  have h1 : sgn (F.eval 0) = sgn F.leadingCoeff :=
    sgn_eval_of_roots_lt hF (fun y hy => absurd hy (hroots y))
  have hnd : (-X : ℝ[X]).natDegree ≠ 0 := by
    rw [natDegree_neg, natDegree_X]
    exact one_ne_zero
  have hlc : (F.comp (-X)).leadingCoeff = F.leadingCoeff * (-1) ^ F.natDegree := by
    rw [leadingCoeff_comp hnd, leadingCoeff_neg, leadingCoeff_X]
  have hFc : F.comp (-X) ≠ 0 := by
    intro h0
    have h5 : F.leadingCoeff * (-1) ^ F.natDegree = 0 := by
      rw [← hlc, h0, leadingCoeff_zero]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hF) (pow_ne_zero _ (by norm_num)) h5
  have h2 : sgn ((F.comp (-X)).eval 0) = sgn (F.comp (-X)).leadingCoeff := by
    refine sgn_eval_of_roots_lt hFc (fun y hy => ?_)
    refine absurd ?_ (hroots (-y))
    have h3 : eval y (F.comp (-X)) = eval (-y) F := by
      rw [eval_comp, eval_neg, eval_X]
    show eval (-y) F = 0
    rw [← h3]
    exact hy
  have h4 : eval 0 (F.comp (-X)) = eval 0 F := by
    rw [eval_comp, eval_neg, eval_X, neg_zero]
  unfold sgnTop sgnBot
  rw [← h1, ← hlc, ← h2, h4]

end

end ST

end GroupApproximation.Full.NN11b
