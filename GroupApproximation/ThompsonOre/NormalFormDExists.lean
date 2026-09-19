/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.ThompsonOre.NormalFormD

/-!
# The normal form of `F_{d,∞}`: list and group lemmas for the reduction rules

This file collects the list lemmas (`padZ`, `split_lowZero`, …) and the group identities used by
`GroupApproximation.ThompsonOre.NormalFormDMul`. There, left multiplication by `x_k^{±1}` sends a
normal form to a normal form (`mulX`, `mulXInv`), and for `k > 0` it leaves the first `k` pairs
unchanged. The reduction rules are:

- `x_{m+1}^{±1} x_0^a = x_0^a x_{m+sa+1}^{±1}`;
- `x_0 φ(φ^s v) x_0⁻¹ = φ(v)`, which cancels `x_0 ⋯ x_0⁻¹` around a tail whose first `s` pairs are
  `(0, 0)`;
- `x_0⁻¹ φ(v) = φ(φ^s v) x_0⁻¹`.

Existence (`FdModel.nf_exists`) and the standard product (`FdModel.val_eq_pos_mul_inv`) are in
`NormalFormDMul`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ThompsonOre

open FNormal FdNormal

namespace FdNormal

/-- Put `n` zero pairs in front, unless the form is empty. -/
def padZ (n : ℕ) (r : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if r = [] then [] else List.replicate n (0, 0) ++ r

theorem getD_replicate_append (z : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    ∀ k i : ℕ, i < k → (List.replicate k z ++ t).getD i (0, 0) = z
  | k + 1, 0, _ => by simp only [List.replicate_succ, List.cons_append, List.getD_cons_zero]
  | k + 1, i + 1, h => by
    simp only [List.replicate_succ, List.cons_append, List.getD_cons_succ]
    exact getD_replicate_append z t k i (by omega)

theorem getD_cons' (e : ℕ × ℕ) (i : ℕ) :
    ∀ r : List (ℕ × ℕ), (cons' e r).getD i (0, 0) = (e :: r).getD i (0, 0)
  | [] => by
    by_cases he : e = (0, 0)
    · subst he
      cases i <;> simp [cons']
    · simp [cons', he]
  | _ :: _ => rfl

theorem isNFd_cons' {s : ℕ} {e : ℕ × ℕ} {r : List (ℕ × ℕ)} (hr : IsNFd s r)
    (h : 0 < e.1 → 0 < e.2 → ¬ lowZero s r) : IsNFd s (cons' e r) := by
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

theorem isNFd_replicate {s : ℕ} (e : ℕ × ℕ) (he : e ≠ (0, 0)) (h2 : ¬ (0 < e.1 ∧ 0 < e.2)) :
    ∀ k, IsNFd s (List.replicate k (0, 0) ++ [e])
  | 0 => ⟨trivial, fun _ => he, fun h1 h3 => absurd ⟨h1, h3⟩ h2⟩
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append]
    exact ⟨isNFd_replicate e he h2 k, fun h => absurd h (by simp),
      fun h => absurd h (lt_irrefl 0)⟩

theorem isNFd_replicate_append {s : ℕ} {r : List (ℕ × ℕ)} (hr : IsNFd s r) (hne : r ≠ []) :
    ∀ n, IsNFd s (List.replicate n (0, 0) ++ r)
  | 0 => hr
  | n + 1 => by
    rw [List.replicate_succ, List.cons_append]
    exact ⟨isNFd_replicate_append hr hne n, fun h => absurd h (by simp [hne]),
      fun h => absurd h (lt_irrefl 0)⟩

theorem isNFd_padZ {s n : ℕ} {r : List (ℕ × ℕ)} (hr : IsNFd s r) : IsNFd s (padZ n r) := by
  by_cases hne : r = []
  · rw [padZ, if_pos hne]
    trivial
  · rw [padZ, if_neg hne]
    exact isNFd_replicate_append hr hne n

/-- A nonempty normal form whose first `s` pairs vanish is `s` zero pairs followed by a normal form. -/
theorem split_lowZero {s : ℕ} : ∀ (n : ℕ) (r : List (ℕ × ℕ)), IsNFd s r → r ≠ [] → lowZero n r →
    ∃ r'', r = List.replicate n (0, 0) ++ r'' ∧ r'' ≠ [] ∧ IsNFd s r''
  | 0, r, hr, hne, _ => ⟨r, rfl, hne, hr⟩
  | _ + 1, [], _, hne, _ => absurd rfl hne
  | n + 1, e :: t, hr, _, hz => by
    obtain ⟨he, ht⟩ := lowZero_succ_cons.mp hz
    subst he
    have htne : t ≠ [] := fun h => hr.2.1 h rfl
    obtain ⟨r'', rfl, h1, h2⟩ := split_lowZero n t hr.1 htne ht
    exact ⟨r'', rfl, h1, h2⟩

end FdNormal

namespace FdModel

variable {G : Type*} [Group G] {s : ℕ} (M : FdModel G s)

theorem val_cons' (e : ℕ × ℕ) : ∀ r : List (ℕ × ℕ), M.val (cons' e r) = M.val (e :: r)
  | [] => by
    by_cases he : e = (0, 0)
    · subst he
      simp [cons']
    · simp [cons', he]
  | _ :: _ => rfl

theorem iterate_shift_one : ∀ n, M.shift^[n] (1 : G) = 1
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', iterate_shift_one n, map_one]

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

theorem val_padZ (n : ℕ) (r : List (ℕ × ℕ)) : M.val (padZ n r) = M.shift^[n] (M.val r) := by
  by_cases hne : r = []
  · rw [padZ, if_pos hne, hne, val_nil, M.iterate_shift_one]
  · rw [padZ, if_neg hne, M.val_replicate]

/-- `x_{m+1} x_0^a = x_0^a x_{m+sa+1}`. -/
theorem x_succ_mul_pow (m : ℕ) : ∀ a : ℕ,
    M.x (m + 1) * M.x 0 ^ a = M.x 0 ^ a * M.x (m + s * a + 1)
  | 0 => by simp
  | a + 1 => by
    have h := M.rel 0 (m + s * a + 1) (by omega)
    rw [show m + s * (a + 1) + 1 = m + s * a + 1 + s by
      rw [Nat.mul_add, Nat.mul_one]; omega]
    calc M.x (m + 1) * M.x 0 ^ (a + 1) = (M.x (m + 1) * M.x 0 ^ a) * M.x 0 := by
          rw [pow_succ, mul_assoc]
      _ = M.x 0 ^ a * (M.x (m + s * a + 1) * M.x 0) := by rw [x_succ_mul_pow m a, mul_assoc]
      _ = M.x 0 ^ a * (M.x 0 * M.x (m + s * a + 1 + s)) := by rw [h]
      _ = M.x 0 ^ (a + 1) * M.x (m + s * a + 1 + s) := by rw [← mul_assoc, ← pow_succ]

theorem inv_x_succ_mul_pow (m a : ℕ) :
    (M.x (m + 1))⁻¹ * M.x 0 ^ a = M.x 0 ^ a * (M.x (m + s * a + 1))⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, M.x_succ_mul_pow, mul_inv_cancel_right]

end FdModel

end GroupApproximation.ThompsonOre
