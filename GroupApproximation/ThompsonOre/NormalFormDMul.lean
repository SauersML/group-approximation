/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.ThompsonOre.NormalFormDExists
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The normal form of `F_{d,∞}`: existence

`mulX` and `mulXInv` show that left multiplication by `x_k^{±1}` sends a normal form to a normal form
and, for `k > 0`, keeps the first `k` pairs. Their cases are the reduction rules listed in
`GroupApproximation.ThompsonOre.NormalFormDExists`. So:
- `FdModel.nf_exists`: every element is the value of a normal form (over any `FdModel`);
- `FdModel.nf_existsUnique`: it is unique;
- `FdModel.val_eq_pos_mul_inv`: its value is `x_0^{a_0} ⋯ x_n^{a_n} · (x_0^{b_0} ⋯ x_n^{b_n})⁻¹`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ThompsonOre

open FNormal FdNormal

theorem FdNormal.lowZero_of_agree {t k : ℕ} {l l' : List (ℕ × ℕ)}
    (h : ∀ i < k, l'.getD i (0, 0) = l.getD i (0, 0)) (ht : t ≤ k) :
    lowZero t l' ↔ lowZero t l :=
  ⟨fun hz i hi => (h i (by omega)).symm.trans (hz i hi),
    fun hz i hi => (h i (by omega)).trans (hz i hi)⟩

namespace FdModel

variable {G : Type*} [Group G] {s : ℕ} (M : FdModel G s)

/-- `x_k · (normal form)` is a normal form with the same first `k` pairs. -/
theorem mulX : ∀ l : List (ℕ × ℕ), IsNFd s l → ∀ k : ℕ,
    ∃ l', IsNFd s l' ∧ M.val l' = M.x k * M.val l ∧ ∀ i < k, l'.getD i (0, 0) = l.getD i (0, 0)
  | [], _, k => ⟨List.replicate k (0, 0) ++ [(1, 0)], isNFd_replicate (1, 0) (by simp) (by simp) k,
      by rw [M.val_replicate]; simp [M.iterate_shift_x],
      fun i hi => by rw [getD_replicate_append _ _ k i hi]; simp⟩
  | (a, b) :: r, hl, 0 => by
    by_cases hc : b = 0 ∨ 0 < a ∨ ¬ lowZero s r
    · refine ⟨(a + 1, b) :: r, ⟨hl.1, fun _ => by simp, fun _ hb => ?_⟩, ?_,
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      · rcases hc with h0 | ha | hr
        · exact absurd h0 (Nat.pos_iff_ne_zero.mp hb)
        · exact hl.2.2 ha hb
        · exact hr
      · rw [val_cons, val_cons, pow_succ']
        simp only [mul_assoc]
    · obtain ⟨hb, ha, hr⟩ : ¬ b = 0 ∧ ¬ 0 < a ∧ ¬ ¬ lowZero s r := by
        simpa only [not_or] using hc
      have hr' : lowZero s r := not_not.mp hr
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      obtain rfl : a = 0 := by omega
      by_cases hne : r = []
      · subst hne
        refine ⟨cons' (0, b') [], isNFd_cons' trivial fun h => absurd h (lt_irrefl 0), ?_,
          fun i hi => absurd hi (Nat.not_lt_zero _)⟩
        rw [M.val_cons', val_cons, val_cons, val_nil, map_one, pow_succ]
        group
      · obtain ⟨r'', rfl, hne'', hr''⟩ := split_lowZero s r hl.1 hne hr'
        refine ⟨(0, b') :: r'', ⟨hr'', fun h => absurd h hne'', fun h => absurd h (lt_irrefl 0)⟩,
          ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
        rw [val_cons, val_cons, M.val_replicate]
        simp only [pow_zero, one_mul]
        rw [← mul_assoc, M.x0_mul_shift_iter, pow_succ]
        group
  | (a, b) :: r, hl, m + 1 => by
    obtain ⟨r', hr', hv, hag⟩ := mulX r hl.1 (m + s * a)
    refine ⟨cons' (a, b) r', isNFd_cons' hr' fun ha hb => ?_, ?_, fun i hi => ?_⟩
    · have ha' : 0 < a := ha
      have hsa : s ≤ s * a := Nat.le_mul_of_pos_right s ha'
      rw [lowZero_of_agree hag (by omega)]
      exact hl.2.2 ha hb
    · rw [M.val_cons', val_cons, val_cons, hv, map_mul, M.shift_x, ← mul_assoc (M.x (m + 1)),
        ← mul_assoc (M.x (m + 1)), M.x_succ_mul_pow]
      simp only [mul_assoc]
    · rw [getD_cons']
      cases i with
      | zero => simp only [List.getD_cons_zero]
      | succ i =>
        simp only [List.getD_cons_succ]
        exact hag i (by omega)

/-- `x_k⁻¹ · (normal form)` is a normal form with the same first `k` pairs. -/
theorem mulXInv : ∀ l : List (ℕ × ℕ), IsNFd s l → ∀ k : ℕ,
    ∃ l', IsNFd s l' ∧ M.val l' = (M.x k)⁻¹ * M.val l ∧
      ∀ i < k, l'.getD i (0, 0) = l.getD i (0, 0)
  | [], _, k => ⟨List.replicate k (0, 0) ++ [(0, 1)], isNFd_replicate (0, 1) (by simp) (by simp) k,
      by rw [M.val_replicate]; simp [M.iterate_shift_inv, M.iterate_shift_x],
      fun i hi => by rw [getD_replicate_append _ _ k i hi]; simp⟩
  | (a, b) :: r, hl, 0 => by
    cases a with
    | succ a =>
      refine ⟨cons' (a, b) r, isNFd_cons' hl.1 fun _ hb => hl.2.2 (Nat.succ_pos a) hb, ?_,
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      rw [M.val_cons', val_cons, val_cons, pow_succ']
      group
    | zero =>
      refine ⟨(0, b + 1) :: padZ s r,
        ⟨isNFd_padZ hl.1, fun _ => by simp, fun h => absurd h (lt_irrefl 0)⟩, ?_,
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      rw [val_cons, val_cons, M.val_padZ]
      simp only [pow_zero, one_mul]
      rw [← mul_assoc, M.inv_x0_mul_shift, pow_succ]
      group
  | (a, b) :: r, hl, m + 1 => by
    obtain ⟨r', hr', hv, hag⟩ := mulXInv r hl.1 (m + s * a)
    refine ⟨cons' (a, b) r', isNFd_cons' hr' fun ha hb => ?_, ?_, fun i hi => ?_⟩
    · have ha' : 0 < a := ha
      have hsa : s ≤ s * a := Nat.le_mul_of_pos_right s ha'
      rw [lowZero_of_agree hag (by omega)]
      exact hl.2.2 ha hb
    · rw [M.val_cons', val_cons, val_cons, hv, map_mul, map_inv, M.shift_x,
        ← mul_assoc (M.x (m + 1))⁻¹, ← mul_assoc (M.x (m + 1))⁻¹, M.inv_x_succ_mul_pow]
      simp only [mul_assoc]
    · rw [getD_cons']
      cases i with
      | zero => simp only [List.getD_cons_zero]
      | succ i =>
        simp only [List.getD_cons_succ]
        exact hag i (by omega)

/-- **Existence of the normal form of `F_{s+1,∞}`.** -/
theorem nf_exists (g : G) : ∃ l, IsNFd s l ∧ M.val l = g := by
  have hg : g ∈ Subgroup.closure (Set.range M.x) := by
    rw [M.closure_eq_top]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨[], trivial, rfl⟩
  | mul_left y hy z _ ih =>
    obtain ⟨k, rfl⟩ := hy
    obtain ⟨l, hl, rfl⟩ := ih
    obtain ⟨l', hl', hv, -⟩ := M.mulX l hl k
    exact ⟨l', hl', hv⟩
  | inv_mul_cancel y hy z _ ih =>
    obtain ⟨k, rfl⟩ := hy
    obtain ⟨l, hl, rfl⟩ := ih
    obtain ⟨l', hl', hv, -⟩ := M.mulXInv l hl k
    exact ⟨l', hl', hv⟩

/-- **Every element of `F_{s+1,∞}` has exactly one normal form.** -/
theorem nf_existsUnique (g : G) : ∃! l, IsNFd s l ∧ M.val l = g := by
  obtain ⟨l, hl, hv⟩ := M.nf_exists g
  exact ⟨l, ⟨hl, hv⟩, fun l' h' => M.nf_unique l' l h'.1 hl (h'.2.trans hv.symm)⟩

/-! ### The standard product -/

/-- `x_k^{a_0} x_{k+1}^{a_1} ⋯` for the first exponents. -/
def posWord : ℕ → List (ℕ × ℕ) → G
  | _, [] => 1
  | k, e :: r => M.x k ^ e.1 * posWord (k + 1) r

/-- `x_k^{b_0} x_{k+1}^{b_1} ⋯` for the second exponents. -/
def negWord : ℕ → List (ℕ × ℕ) → G
  | _, [] => 1
  | k, e :: r => M.x k ^ e.2 * negWord (k + 1) r

theorem shift_posWord : ∀ (k : ℕ) (l : List (ℕ × ℕ)), M.shift (M.posWord k l) = M.posWord (k + 1) l
  | _, [] => map_one _
  | k, e :: r => by
    show M.shift (M.x k ^ e.1 * M.posWord (k + 1) r) = M.x (k + 1) ^ e.1 * M.posWord (k + 1 + 1) r
    rw [map_mul, map_pow, M.shift_x, shift_posWord (k + 1) r]

theorem shift_negWord : ∀ (k : ℕ) (l : List (ℕ × ℕ)), M.shift (M.negWord k l) = M.negWord (k + 1) l
  | _, [] => map_one _
  | k, e :: r => by
    show M.shift (M.x k ^ e.2 * M.negWord (k + 1) r) = M.x (k + 1) ^ e.2 * M.negWord (k + 1 + 1) r
    rw [map_mul, map_pow, M.shift_x, shift_negWord (k + 1) r]

/-- **The standard form**: `val [(a_0, b_0), …, (a_n, b_n)] = x_0^{a_0} ⋯ x_n^{a_n} · x_n^{-b_n} ⋯
x_0^{-b_0}`. -/
theorem val_eq_pos_mul_inv : ∀ l : List (ℕ × ℕ), M.val l = M.posWord 0 l * (M.negWord 0 l)⁻¹
  | [] => by simp [posWord, negWord]
  | (a, b) :: r => by
    show M.x 0 ^ a * M.shift (M.val r) * (M.x 0 ^ b)⁻¹ =
      M.x 0 ^ a * M.posWord (0 + 1) r * (M.x 0 ^ b * M.negWord (0 + 1) r)⁻¹
    rw [val_eq_pos_mul_inv r, map_mul, map_inv, M.shift_posWord, M.shift_negWord]
    group

end FdModel

end GroupApproximation.ThompsonOre
