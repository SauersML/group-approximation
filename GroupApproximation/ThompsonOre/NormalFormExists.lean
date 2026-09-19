/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.ThompsonOre.NormalForm
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.List.Basic

/-!
# The normal form of Thompson's group `F`: the reduction rules and existence

Left multiplication by a generator `x_k^{±1}` sends a normal form to a normal form. The cases of
`mulX` and `mulXInv` are the reduction rules:

- `x_{m+1}^{±1} x_0^a = x_0^a x_{m+a+1}^{±1}` moves the letter past `x_0^a`, into the tail
  (`x_succ_mul_pow`, `inv_x_succ_mul_pow`);
- `x_0 x_0^a = x_0^{a+1}` and `x_0⁻¹ x_0^{a+1} = x_0^a` change the first exponent;
- `x_0 φ²(v) x_0⁻¹ = φ(v)` cancels an `x_0 … x_0⁻¹` pair around a tail that does not start with
  `x_1^{±1}`, and lowers every index by one (`x0_mul_shift_shift`);
- `x_0⁻¹ φ(v) = φ²(v) x_0⁻¹` moves `x_0⁻¹` to the right end (`inv_x0_mul_shift`).

`cons'` drops a trailing `(0, 0)`.

So every element is the value of a normal form (`FModel.nf_exists`). With `FModel.nf_unique` the
form is unique (`FModel.nf_existsUnique`). `val_eq_pos_mul_inv` reads a form as
`x_0^{a_0} ⋯ x_n^{a_n} · (x_0^{b_0} ⋯ x_n^{b_n})⁻¹`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ThompsonOre

namespace FNormal

/-- Prepend a pair, dropping it when it would be a trailing `(0, 0)`. -/
def cons' (e : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => if e = (0, 0) then [] else [e]
  | h :: t => e :: h :: t

theorem lead_cons' (e : ℕ × ℕ) : ∀ r : List (ℕ × ℕ), lead (cons' e r) = e
  | [] => by
    by_cases he : e = (0, 0)
    · simp [cons', he]
    · simp [cons', he]
  | _ :: _ => rfl

theorem isNF_cons' {e : ℕ × ℕ} {r : List (ℕ × ℕ)} (hr : IsNF r)
    (h : 0 < e.1 → 0 < e.2 → lead r ≠ (0, 0)) : IsNF (cons' e r) := by
  cases r with
  | nil =>
    by_cases he : e = (0, 0)
    · have h1 : cons' e [] = [] := by simp [cons', he]
      rw [h1]
      trivial
    · have h1 : cons' e [] = [e] := by simp [cons', he]
      rw [h1]
      exact ⟨trivial, fun _ => he, h⟩
  | cons a t => exact ⟨hr, fun h' => absurd h' (List.cons_ne_nil a t), h⟩

theorem isNF_replicate (e : ℕ × ℕ) (he : e ≠ (0, 0)) (h2 : ¬ (0 < e.1 ∧ 0 < e.2)) :
    ∀ k, IsNF (List.replicate k (0, 0) ++ [e])
  | 0 => ⟨trivial, fun _ => he, fun h1 h3 => absurd ⟨h1, h3⟩ h2⟩
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append]
    exact ⟨isNF_replicate e he h2 k, fun h => absurd h (by simp), fun h => absurd h (lt_irrefl 0)⟩

end FNormal

open FNormal

namespace FModel

variable {G : Type*} [Group G] (M : FModel G)

theorem val_cons' (e : ℕ × ℕ) : ∀ r : List (ℕ × ℕ), M.val (cons' e r) = M.val (e :: r)
  | [] => by
    by_cases he : e = (0, 0)
    · subst he
      simp [cons']
    · simp [cons', he]
  | _ :: _ => rfl

theorem iterate_shift_x (n : ℕ) : ∀ k, M.shift^[k] (M.x n) = M.x (n + k)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_shift_x n k, M.shift_x, Nat.add_assoc]

theorem iterate_shift_inv (g : G) : ∀ k, M.shift^[k] g⁻¹ = (M.shift^[k] g)⁻¹
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_shift_inv g k, map_inv]

theorem val_replicate (l : List (ℕ × ℕ)) :
    ∀ k, M.val (List.replicate k (0, 0) ++ l) = M.shift^[k] (M.val l)
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append, val_cons, val_replicate l k,
      Function.iterate_succ_apply']
    simp

/-- `x_{m+1} x_0^a = x_0^a x_{m+a+1}`. -/
theorem x_succ_mul_pow (m : ℕ) : ∀ a : ℕ, M.x (m + 1) * M.x 0 ^ a = M.x 0 ^ a * M.x (m + a + 1)
  | 0 => by simp
  | a + 1 => by
    have h := M.rel 0 (m + a + 1) (by omega)
    rw [show m + (a + 1) + 1 = m + a + 1 + 1 by omega]
    calc M.x (m + 1) * M.x 0 ^ (a + 1) = (M.x (m + 1) * M.x 0 ^ a) * M.x 0 := by
          rw [pow_succ, mul_assoc]
      _ = M.x 0 ^ a * (M.x (m + a + 1) * M.x 0) := by rw [x_succ_mul_pow m a, mul_assoc]
      _ = M.x 0 ^ a * (M.x 0 * M.x (m + a + 1 + 1)) := by rw [h]
      _ = M.x 0 ^ (a + 1) * M.x (m + a + 1 + 1) := by rw [← mul_assoc, ← pow_succ]

/-- `x_{m+1}⁻¹ x_0^a = x_0^a x_{m+a+1}⁻¹`. -/
theorem inv_x_succ_mul_pow (m a : ℕ) :
    (M.x (m + 1))⁻¹ * M.x 0 ^ a = M.x 0 ^ a * (M.x (m + a + 1))⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, M.x_succ_mul_pow, mul_inv_cancel_right]

/-! ### Left multiplication by `x_k` -/

/-- `x_k · (normal form)` is a normal form; for `k > 0` the first pair is unchanged. -/
theorem mulX : ∀ l : List (ℕ × ℕ), IsNF l → ∀ k : ℕ,
    ∃ l', IsNF l' ∧ M.val l' = M.x k * M.val l ∧ (0 < k → lead l' = lead l)
  | [], _, k => ⟨List.replicate k (0, 0) ++ [(1, 0)], isNF_replicate (1, 0) (by simp) (by simp) k,
      by rw [M.val_replicate]; simp [M.iterate_shift_x],
      fun hk => by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rfl⟩
  | (a, b) :: r, hl, 0 => by
    by_cases hc : b = 0 ∨ 0 < a ∨ lead r ≠ (0, 0)
    · refine ⟨(a + 1, b) :: r, ⟨hl.1, fun _ => by simp, fun _ hb => ?_⟩, ?_,
        fun h => absurd h (lt_irrefl 0)⟩
      · rcases hc with h0 | ha | hr
        · exact absurd h0 (Nat.pos_iff_ne_zero.mp hb)
        · exact hl.2.2 ha hb
        · exact hr
      · rw [val_cons, val_cons, pow_succ']
        simp only [mul_assoc]
    · obtain ⟨hb, ha, hr⟩ : ¬ b = 0 ∧ ¬ 0 < a ∧ ¬ lead r ≠ (0, 0) := by
        simpa only [not_or] using hc
      have hr' : lead r = (0, 0) := by
        by_contra h'
        exact hr h'
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      obtain rfl : a = 0 := by omega
      cases r with
      | nil =>
        refine ⟨cons' (0, b') [], isNF_cons' trivial fun h => absurd h (lt_irrefl 0), ?_,
          fun h => absurd h (lt_irrefl 0)⟩
        rw [M.val_cons', val_cons, val_cons, val_nil, map_one, pow_succ]
        group
      | cons e r'' =>
        have he : e = (0, 0) := hr'
        subst he
        have hr'' : r'' ≠ [] := fun h => hl.1.2.1 h rfl
        refine ⟨(0, b') :: r'', ⟨hl.1.1, fun h => absurd h hr'', fun h => absurd h (lt_irrefl 0)⟩,
          ?_, fun h => absurd h (lt_irrefl 0)⟩
        simp only [val_cons, pow_zero, one_mul, inv_one, mul_one]
        rw [← mul_assoc, M.x0_mul_shift_shift, pow_succ]
        group
  | (a, b) :: r, hl, m + 1 => by
    obtain ⟨r', hr', hv, hlead⟩ := mulX r hl.1 (m + a)
    refine ⟨cons' (a, b) r', isNF_cons' hr' fun ha hb => ?_, ?_, fun _ => lead_cons' _ _⟩
    · have ha' : 0 < a := ha
      rw [hlead (by omega)]
      exact hl.2.2 ha hb
    · rw [M.val_cons', val_cons, val_cons, hv, map_mul, M.shift_x, ← mul_assoc (M.x (m + 1)),
        ← mul_assoc (M.x (m + 1)), M.x_succ_mul_pow]
      simp only [mul_assoc]

/-- `x_k⁻¹ · (normal form)` is a normal form; for `k > 0` the first pair is unchanged. -/
theorem mulXInv : ∀ l : List (ℕ × ℕ), IsNF l → ∀ k : ℕ,
    ∃ l', IsNF l' ∧ M.val l' = (M.x k)⁻¹ * M.val l ∧ (0 < k → lead l' = lead l)
  | [], _, k => ⟨List.replicate k (0, 0) ++ [(0, 1)], isNF_replicate (0, 1) (by simp) (by simp) k,
      by rw [M.val_replicate]; simp [M.iterate_shift_inv, M.iterate_shift_x],
      fun hk => by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rfl⟩
  | (a, b) :: r, hl, 0 => by
    cases a with
    | succ a =>
      refine ⟨cons' (a, b) r, isNF_cons' hl.1 fun _ hb => hl.2.2 (Nat.succ_pos a) hb, ?_,
        fun h => absurd h (lt_irrefl 0)⟩
      rw [M.val_cons', val_cons, val_cons, pow_succ']
      group
    | zero =>
      refine ⟨(0, b + 1) :: cons' (0, 0) r,
        ⟨isNF_cons' hl.1 fun h => absurd h (lt_irrefl 0), fun _ => by simp,
          fun h => absurd h (lt_irrefl 0)⟩, ?_, fun h => absurd h (lt_irrefl 0)⟩
      simp only [val_cons, M.val_cons', pow_zero, one_mul, inv_one, mul_one]
      rw [← mul_assoc, M.inv_x0_mul_shift, pow_succ]
      group
  | (a, b) :: r, hl, m + 1 => by
    obtain ⟨r', hr', hv, hlead⟩ := mulXInv r hl.1 (m + a)
    refine ⟨cons' (a, b) r', isNF_cons' hr' fun ha hb => ?_, ?_, fun _ => lead_cons' _ _⟩
    · have ha' : 0 < a := ha
      rw [hlead (by omega)]
      exact hl.2.2 ha hb
    · rw [M.val_cons', val_cons, val_cons, hv, map_mul, map_inv, M.shift_x,
        ← mul_assoc (M.x (m + 1))⁻¹, ← mul_assoc (M.x (m + 1))⁻¹, M.inv_x_succ_mul_pow]
      simp only [mul_assoc]

/-! ### Existence and uniqueness -/

/-- **Existence of the normal form.** -/
theorem nf_exists (g : G) : ∃ l, IsNF l ∧ M.val l = g := by
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

/-- **Every element has exactly one normal form.** -/
theorem nf_existsUnique (g : G) : ∃! l, IsNF l ∧ M.val l = g := by
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

end FModel

end GroupApproximation.ThompsonOre
