/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.ThompsonOre.NormalFormExists

/-!
# The normal form of `F_{d,∞}`: definitions and uniqueness

`F_{d,∞} = ⟨x_0, x_1, … | x_j x_i = x_i x_{j+s} (i < j)⟩` with step `s = d - 1`; `s = 1` is Thompson's `F`.
Forms are exponent lists `[(a_0, b_0), …, (a_n, b_n)]` with value
`x_0^{a_0} ⋯ x_n^{a_n} · x_n^{-b_n} ⋯ x_0^{-b_0}`, defined from the smallest index up as in
`GroupApproximation.ThompsonOre.NormalForm`. The normal-form condition (`FdNormal.IsNFd s`) is:
- the last pair is not `(0, 0)`;
- if `a_i > 0` and `b_i > 0`, then one of the pairs `i+1, …, i+s` is not `(0, 0)`.

This is the Brown–Stein normal form. `x_i u x_i⁻¹` lowers every index of `u` by `s` when all of them
are at least `i + s + 1`, so that is exactly the pattern that can still be reduced.

`FdModel G s` is `FModel` with the relation `x_j x_i = x_i x_{j+s}`. The uniqueness proof is
`FModel.nf_unique` with two changes:
- `x_0⁻¹ φ(g) x_0 = φ(φ^s g)` (`conj_shift`);
- `val_ne_iter`: a form with a nonzero pair among its first `t` is not in the image of `φ^t`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ThompsonOre

open FNormal

namespace FdNormal

/-- The first `t` pairs are all `(0, 0)`. -/
def lowZero (t : ℕ) (l : List (ℕ × ℕ)) : Prop := ∀ i < t, l.getD i (0, 0) = (0, 0)

theorem lowZero_zero (l : List (ℕ × ℕ)) : lowZero 0 l := fun _ h => absurd h (Nat.not_lt_zero _)

theorem lowZero_nil (t : ℕ) : lowZero t [] := fun _ _ => by simp

theorem lowZero_succ_cons {t : ℕ} {e : ℕ × ℕ} {r : List (ℕ × ℕ)} :
    lowZero (t + 1) (e :: r) ↔ e = (0, 0) ∧ lowZero t r := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (Nat.succ_pos t), fun i hi => ?_⟩
    simpa using h (i + 1) (by omega)
  · rintro ⟨he, hr⟩ i hi
    cases i with
    | zero => simp [he]
    | succ i => simpa using hr i (by omega)

/-- The normal-form conditions for step `s`. -/
def IsNFd (s : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | e :: r => IsNFd s r ∧ (r = [] → e ≠ (0, 0)) ∧ (0 < e.1 → 0 < e.2 → ¬ lowZero s r)

end FdNormal

open FdNormal

/-- A model of `F_{s+1,∞}` with its shift and its `x_0`-exponent. -/
structure FdModel (G : Type*) [Group G] (s : ℕ) where
  /-- The generators `x_0, x_1, …`. -/
  x : ℕ → G
  rel : ∀ i j : ℕ, i < j → x j * x i = x i * x (j + s)
  closure_eq_top : Subgroup.closure (Set.range x) = ⊤
  /-- The shift `x_n ↦ x_{n+1}`. -/
  shift : G →* G
  shift_x : ∀ n, shift (x n) = x (n + 1)
  shift_injective : Function.Injective shift
  /-- The exponent sum of `x_0`. -/
  chi : G →* Multiplicative ℤ
  chi_x_zero : chi (x 0) = Multiplicative.ofAdd 1
  chi_x_succ : ∀ n, chi (x (n + 1)) = 1

namespace FdModel

variable {G : Type*} [Group G] {s : ℕ} (M : FdModel G s)

/-- The value of an exponent list: `val ((a, b) :: r) = x_0^a · φ(val r) · x_0^{-b}`. -/
def val : List (ℕ × ℕ) → G
  | [] => 1
  | e :: r => M.x 0 ^ e.1 * M.shift (val r) * (M.x 0 ^ e.2)⁻¹

@[simp] theorem val_nil : M.val [] = 1 := rfl

@[simp] theorem val_cons (a b : ℕ) (r : List (ℕ × ℕ)) :
    M.val ((a, b) :: r) = M.x 0 ^ a * M.shift (M.val r) * (M.x 0 ^ b)⁻¹ := rfl

theorem val_eq_lead : ∀ l : List (ℕ × ℕ),
    M.val l = M.x 0 ^ (lead l).1 * M.shift (M.val l.tail) * (M.x 0 ^ (lead l).2)⁻¹
  | [] => by simp
  | _ :: _ => rfl

/-- `φ^n` as a homomorphism. -/
def shiftPow : ℕ → G →* G
  | 0 => MonoidHom.id G
  | n + 1 => M.shift.comp (shiftPow n)

theorem shiftPow_apply : ∀ (n : ℕ) (g : G), M.shiftPow n g = M.shift^[n] g
  | 0, _ => rfl
  | n + 1, g => by
    show M.shift (M.shiftPow n g) = M.shift^[n + 1] g
    rw [Function.iterate_succ_apply', shiftPow_apply n g]

theorem iterate_shift_x (n : ℕ) : ∀ k, M.shift^[k] (M.x n) = M.x (n + k)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_shift_x n k, M.shift_x, Nat.add_assoc]

/-- `x_0⁻¹ φ(g) x_0 = φ(φ^s g)`. -/
theorem conj_shift (g : G) : (M.x 0)⁻¹ * M.shift g * M.x 0 = M.shift (M.shift^[s] g) := by
  have h : (MulAut.conj (M.x 0)⁻¹).toMonoidHom.comp M.shift = M.shift.comp (M.shiftPow s) := by
    refine MonoidHom.eq_of_eqOn_dense M.closure_eq_top ?_
    rintro _ ⟨n, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      M.shift_x, M.shiftPow_apply, M.iterate_shift_x]
    rw [mul_assoc, M.rel 0 (n + 1) (by omega), ← mul_assoc, inv_mul_cancel, one_mul,
      Nat.add_right_comm]
  have h2 := DFunLike.congr_fun h g
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    M.shiftPow_apply] using h2

/-- `x_0^{-e} φ(g) x_0^e = φ(φ^{s e} g)`. -/
theorem conj_pow (g : G) : ∀ e : ℕ,
    (M.x 0 ^ e)⁻¹ * M.shift g * M.x 0 ^ e = M.shift (M.shift^[s * e] g)
  | 0 => by simp
  | e + 1 => by
    rw [show s * (e + 1) = s + s * e by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm],
      Function.iterate_add_apply, ← M.conj_shift, ← conj_pow g e, pow_succ]
    group

theorem x0_mul_shift_iter (g : G) : M.x 0 * M.shift (M.shift^[s] g) = M.shift g * M.x 0 := by
  rw [← M.conj_shift]
  group

theorem inv_x0_mul_shift (g : G) :
    (M.x 0)⁻¹ * M.shift g = M.shift (M.shift^[s] g) * (M.x 0)⁻¹ := by
  rw [← M.conj_shift]
  group

theorem chi_shift (g : G) : M.chi (M.shift g) = 1 := by
  have h : M.chi.comp M.shift = 1 := by
    refine MonoidHom.eq_of_eqOn_dense M.closure_eq_top ?_
    rintro _ ⟨n, rfl⟩
    simp only [MonoidHom.comp_apply, M.shift_x, M.chi_x_succ, MonoidHom.one_apply]
  exact DFunLike.congr_fun h g

theorem toAdd_chi_val (l : List (ℕ × ℕ)) :
    Multiplicative.toAdd (M.chi (M.val l)) = ((lead l).1 : ℤ) - (lead l).2 := by
  rw [M.val_eq_lead l, map_mul, map_mul, map_inv, map_pow, map_pow, M.chi_x_zero, M.chi_shift,
    toAdd_mul, toAdd_mul, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_one]
  simp only [nsmul_eq_mul, mul_one, add_zero, sub_eq_add_neg]

/-! ### Uniqueness -/

/-- A form with a nonzero pair among its first `t` is not a `t`-fold shift. -/
theorem val_ne_iter : ∀ l : List (ℕ × ℕ), IsNFd s l → ∀ t, ¬ lowZero t l →
    ∀ w, M.val l ≠ M.shift^[t] w
  | [], _, t, h, _, _ => h (lowZero_nil t)
  | _ :: _, _, 0, h, _, _ => h (lowZero_zero _)
  | (a, b) :: r, hl, t + 1, h, w, hw => by
    rw [Function.iterate_succ_apply'] at hw
    have hab : a = b := by
      have h1 := congrArg (fun g => Multiplicative.toAdd (M.chi g)) hw
      simp only [M.toAdd_chi_val, M.chi_shift, toAdd_one, lead_cons] at h1
      omega
    by_cases ha : a = 0
    · have hb : b = 0 := by omega
      subst ha
      subst hb
      have hr : ¬ lowZero t r := fun h' => h (lowZero_succ_cons.mpr ⟨rfl, h'⟩)
      have e1 : M.val r = M.shift^[t] w := by
        apply M.shift_injective
        rw [← hw, val_cons]
        group
      exact val_ne_iter r hl.1 t hr w e1
    · have ha' : 0 < a := Nat.pos_of_ne_zero ha
      have hb : 0 < b := by omega
      have hr : ¬ lowZero s r := hl.2.2 ha' hb
      have e1 : M.shift (M.val r) = M.shift (M.shift^[s * a] (M.shift^[t] w)) := by
        rw [← M.conj_pow, ← hw, val_cons, ← hab]
        group
      have e2 := M.shift_injective e1
      obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
      rw [show s * (k + 1) = s + s * k by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm],
        Function.iterate_add_apply] at e2
      exact val_ne_iter r hl.1 s hr _ e2

theorem tail_ne_iter {l : List (ℕ × ℕ)} (hl : IsNFd s l) (ha : 0 < (lead l).1)
    (hb : 0 < (lead l).2) : ∀ w, M.val l.tail ≠ M.shift^[s] w := by
  cases l with
  | nil => exact absurd ha (lt_irrefl 0)
  | cons _ r => exact M.val_ne_iter r hl.1 s (hl.2.2 ha hb)

theorem core_step {a b c d : ℕ} {u u' : G} (hno : 0 < c → 0 < d → ∀ w, u' ≠ M.shift^[s] w)
    (hχ : (a : ℤ) - b = (c : ℤ) - d)
    (h : M.x 0 ^ a * M.shift u * (M.x 0 ^ b)⁻¹ = M.x 0 ^ c * M.shift u' * (M.x 0 ^ d)⁻¹) :
    ¬ a < c := by
  intro hlt
  obtain ⟨e, rfl⟩ : ∃ e, c = a + (e + 1) := ⟨c - a - 1, by omega⟩
  obtain rfl : d = b + (e + 1) := by omega
  have e1 := FModel.aux_conj h
  rw [M.conj_pow] at e1
  have e2 := M.shift_injective e1
  rw [show s * (e + 1) = s + s * e by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm],
    Function.iterate_add_apply] at e2
  exact hno (by omega) (by omega) _ e2

theorem lead_eq_of_val_eq {l l' : List (ℕ × ℕ)} (hl : IsNFd s l) (hl' : IsNFd s l')
    (h : M.val l = M.val l') : lead l = lead l' ∧ M.val l.tail = M.val l'.tail := by
  have hχ : ((lead l).1 : ℤ) - (lead l).2 = ((lead l').1 : ℤ) - (lead l').2 := by
    rw [← M.toAdd_chi_val, ← M.toAdd_chi_val, h]
  rw [M.val_eq_lead l, M.val_eq_lead l'] at h
  have h1 := M.core_step (M.tail_ne_iter hl') hχ h
  have h2 := M.core_step (M.tail_ne_iter hl) hχ.symm h.symm
  have ha : (lead l).1 = (lead l').1 := by omega
  have hb : (lead l).2 = (lead l').2 := by omega
  refine ⟨Prod.ext ha hb, M.shift_injective ?_⟩
  rw [ha, hb] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem eq_nil_of_val_eq_one : ∀ l : List (ℕ × ℕ), IsNFd s l → M.val l = 1 → l = []
  | [], _, _ => rfl
  | e :: r, hl, h => by
    obtain ⟨h1, h2⟩ := M.lead_eq_of_val_eq (l' := []) hl trivial h
    have h2' : M.val r = 1 := h2
    have hr : r = [] := eq_nil_of_val_eq_one r hl.1 h2'
    exact absurd h1 (hl.2.1 hr)

/-- **Uniqueness of the normal form of `F_{s+1,∞}`.** -/
theorem nf_unique : ∀ l l' : List (ℕ × ℕ), IsNFd s l → IsNFd s l' → M.val l = M.val l' → l = l'
  | [], l', _, hl', h => (M.eq_nil_of_val_eq_one l' hl' h.symm).symm
  | _ :: _, [], hl, _, h => M.eq_nil_of_val_eq_one _ hl h
  | e :: r, e' :: r', hl, hl', h => by
    obtain ⟨h1, h2⟩ := M.lead_eq_of_val_eq hl hl' h
    have h2' : M.val r = M.val r' := h2
    have h1' : e = e' := h1
    rw [nf_unique r r' hl.1 hl'.1 h2', h1']

end FdModel

end GroupApproximation.ThompsonOre
