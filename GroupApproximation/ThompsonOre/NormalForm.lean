/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Group

/-!
# The normal form of Thompson's group `F`: definitions and uniqueness

Write `F = ⟨x_0, x_1, … | x_i⁻¹ x_j x_i = x_{j+1} (i < j)⟩`. Every element has a unique normal form
(Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*, Theorem 2.5):

  `x_0^{a_0} x_1^{a_1} ⋯ x_n^{a_n} · x_n^{-b_n} ⋯ x_1^{-b_1} x_0^{-b_0}`,

where, whenever `a_i > 0` and `b_i > 0`, also `a_{i+1} > 0` or `b_{i+1} > 0`, and `(a_n, b_n) ≠ (0, 0)`.
The identity is the empty form.

## Encoding

A form is the list of exponent pairs `[(a_0, b_0), …, (a_n, b_n)]` (`FNormal.IsNF` states the two
conditions). Its value is defined from the smallest index up:
`val ((a, b) :: r) = x_0^a · φ(val r) · x_0^{-b}`, where `φ` is the shift `x_n ↦ x_{n+1}`.
`val_eq_pos_mul_inv` (in `NormalFormExists`) reads it back as the product above.

## The model

`FModel G` bundles what the proofs use:
- elements `x n` with `x_j x_i = x_i x_{j+1}` (`i < j`) that generate `G`;
- an injective endomorphism `shift` with `shift (x n) = x (n + 1)`;
- a homomorphism `chi : G → ℤ` with `chi x_0 = 1` and `chi x_{n+1} = 0` (the `x_0`-exponent).
`GroupApproximation.ThompsonOre.NormalFormF` builds one for `ThompsonF`.

## Uniqueness (`FModel.nf_unique`)

The proof is by induction on the list. Two facts drive it:
- `conj_pow`: `x_0^{-e} φ(g) x_0^e = φ(φ^e g)`;
- `val_ne_shift`: a normal form whose first pair is not `(0, 0)` is not in the image of `φ`.
  For `a ≠ b` this is `chi`; for `a = b > 0` it uses the normal-form condition and induction.

The existence half, whose steps are the reduction rules, is `NormalFormExists`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ThompsonOre

/-! ### Forms as lists of exponent pairs -/

namespace FNormal

/-- The first exponent pair, `(0, 0)` for the empty form. -/
def lead (l : List (ℕ × ℕ)) : ℕ × ℕ := l.headD (0, 0)

@[simp] theorem lead_nil : lead [] = (0, 0) := rfl

@[simp] theorem lead_cons (e : ℕ × ℕ) (r : List (ℕ × ℕ)) : lead (e :: r) = e := rfl

/-- The normal-form conditions: the last pair is not `(0, 0)`, and if `x_i` and `x_i⁻¹` both occur
then `x_{i+1}` or `x_{i+1}⁻¹` occurs. -/
def IsNF : List (ℕ × ℕ) → Prop
  | [] => True
  | e :: r => IsNF r ∧ (r = [] → e ≠ (0, 0)) ∧ (0 < e.1 → 0 < e.2 → lead r ≠ (0, 0))

theorem isNF_cons_iff {e : ℕ × ℕ} {r : List (ℕ × ℕ)} :
    IsNF (e :: r) ↔ IsNF r ∧ (r = [] → e ≠ (0, 0)) ∧ (0 < e.1 → 0 < e.2 → lead r ≠ (0, 0)) :=
  Iff.rfl

end FNormal

open FNormal

/-- A model of Thompson's group `F` with its shift and its `x_0`-exponent. -/
structure FModel (G : Type*) [Group G] where
  /-- The generators `x_0, x_1, …`. -/
  x : ℕ → G
  rel : ∀ i j : ℕ, i < j → x j * x i = x i * x (j + 1)
  closure_eq_top : Subgroup.closure (Set.range x) = ⊤
  /-- The shift `x_n ↦ x_{n+1}`. -/
  shift : G →* G
  shift_x : ∀ n, shift (x n) = x (n + 1)
  shift_injective : Function.Injective shift
  /-- The exponent sum of `x_0`. -/
  chi : G →* Multiplicative ℤ
  chi_x_zero : chi (x 0) = Multiplicative.ofAdd 1
  chi_x_succ : ∀ n, chi (x (n + 1)) = 1

namespace FModel

variable {G : Type*} [Group G] (M : FModel G)

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

/-! ### The shift and the `x_0`-exponent -/

/-- `x_0⁻¹ φ(g) x_0 = φ(φ(g))`. -/
theorem conj_shift (g : G) : (M.x 0)⁻¹ * M.shift g * M.x 0 = M.shift (M.shift g) := by
  have h : (MulAut.conj (M.x 0)⁻¹).toMonoidHom.comp M.shift = M.shift.comp M.shift := by
    refine MonoidHom.eq_of_eqOn_dense M.closure_eq_top ?_
    rintro _ ⟨n, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      M.shift_x]
    rw [mul_assoc, M.rel 0 (n + 1) (by omega), ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 := DFunLike.congr_fun h g
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    using h2

/-- `x_0^{-e} φ(g) x_0^e = φ(φ^e(g))`. -/
theorem conj_pow (g : G) : ∀ e : ℕ,
    (M.x 0 ^ e)⁻¹ * M.shift g * M.x 0 ^ e = M.shift (M.shift^[e] g)
  | 0 => by simp
  | e + 1 => by
    rw [Function.iterate_succ_apply', ← M.conj_shift, ← conj_pow g e, pow_succ]
    group

theorem x0_mul_shift_shift (g : G) : M.x 0 * M.shift (M.shift g) = M.shift g * M.x 0 := by
  rw [← M.conj_shift]
  group

theorem inv_x0_mul_shift (g : G) : (M.x 0)⁻¹ * M.shift g = M.shift (M.shift g) * (M.x 0)⁻¹ := by
  rw [← M.conj_shift]
  group

theorem chi_shift (g : G) : M.chi (M.shift g) = 1 := by
  have h : M.chi.comp M.shift = 1 := by
    refine MonoidHom.eq_of_eqOn_dense M.closure_eq_top ?_
    rintro _ ⟨n, rfl⟩
    simp only [MonoidHom.comp_apply, M.shift_x, M.chi_x_succ, MonoidHom.one_apply]
  exact DFunLike.congr_fun h g

/-- The `x_0`-exponent of a form is `a_0 - b_0`. -/
theorem toAdd_chi_val (l : List (ℕ × ℕ)) :
    Multiplicative.toAdd (M.chi (M.val l)) = ((lead l).1 : ℤ) - (lead l).2 := by
  rw [M.val_eq_lead l, map_mul, map_mul, map_inv, map_pow, map_pow, M.chi_x_zero, M.chi_shift,
    toAdd_mul, toAdd_mul, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_one]
  simp only [nsmul_eq_mul, mul_one, add_zero, sub_eq_add_neg]

/-! ### Uniqueness -/

/-- A normal form whose first pair is not `(0, 0)` is not a shift. -/
theorem val_ne_shift : ∀ l : List (ℕ × ℕ), IsNF l → lead l ≠ (0, 0) → ∀ w, M.val l ≠ M.shift w
  | [], _, h, _, _ => h rfl
  | (a, b) :: r, hl, h, w, hw => by
    have hab : a = b := by
      have h1 := congrArg (fun g => Multiplicative.toAdd (M.chi g)) hw
      simp only [M.toAdd_chi_val, M.chi_shift, toAdd_one, lead_cons] at h1
      omega
    have ha : 0 < a := Nat.pos_of_ne_zero fun h0 => h (by rw [lead_cons, ← hab, h0])
    have hb : 0 < b := by omega
    have hlead : lead r ≠ (0, 0) := hl.2.2 ha hb
    have e1 : M.shift (M.val r) = M.shift (M.shift^[a] w) := by
      rw [← M.conj_pow, ← hw, val_cons, ← hab]
      group
    have e2 := M.shift_injective e1
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    rw [Function.iterate_succ_apply'] at e2
    exact val_ne_shift r hl.1 hlead _ e2

theorem tail_ne_shift {l : List (ℕ × ℕ)} (hl : IsNF l) (ha : 0 < (lead l).1)
    (hb : 0 < (lead l).2) : ∀ w, M.val l.tail ≠ M.shift w := by
  cases l with
  | nil => exact absurd ha (lt_irrefl 0)
  | cons _ r => exact M.val_ne_shift r hl.1 (hl.2.2 ha hb)

/-- Pure group algebra: `t^a u t^{-b} = t^{a+e} u' t^{-(b+e)}` gives `u' = t^{-e} u t^e`. -/
theorem aux_conj {t u u' : G} {a b e : ℕ}
    (h : t ^ a * u * (t ^ b)⁻¹ = t ^ (a + e) * u' * (t ^ (b + e))⁻¹) :
    u' = (t ^ e)⁻¹ * u * t ^ e := by
  rw [pow_add, pow_add] at h
  calc u' = (t ^ e)⁻¹ * (t ^ a)⁻¹ * (t ^ a * t ^ e * u' * (t ^ b * t ^ e)⁻¹) * (t ^ b * t ^ e) := by
        group
    _ = (t ^ e)⁻¹ * u * t ^ e := by
        rw [← h]
        group

/-- The core step: the first exponent of `x_0` cannot differ. -/
theorem core_step {a b c d : ℕ} {u u' : G} (hno : 0 < c → 0 < d → ∀ w, u' ≠ M.shift w)
    (hχ : (a : ℤ) - b = (c : ℤ) - d)
    (h : M.x 0 ^ a * M.shift u * (M.x 0 ^ b)⁻¹ = M.x 0 ^ c * M.shift u' * (M.x 0 ^ d)⁻¹) :
    ¬ a < c := by
  intro hlt
  obtain ⟨e, rfl⟩ : ∃ e, c = a + (e + 1) := ⟨c - a - 1, by omega⟩
  obtain rfl : d = b + (e + 1) := by omega
  have e1 := aux_conj h
  rw [M.conj_pow] at e1
  have e2 := M.shift_injective e1
  rw [Function.iterate_succ_apply'] at e2
  exact hno (by omega) (by omega) _ e2

theorem lead_eq_of_val_eq {l l' : List (ℕ × ℕ)} (hl : IsNF l) (hl' : IsNF l')
    (h : M.val l = M.val l') : lead l = lead l' ∧ M.val l.tail = M.val l'.tail := by
  have hχ : ((lead l).1 : ℤ) - (lead l).2 = ((lead l').1 : ℤ) - (lead l').2 := by
    rw [← M.toAdd_chi_val, ← M.toAdd_chi_val, h]
  rw [M.val_eq_lead l, M.val_eq_lead l'] at h
  have h1 := M.core_step (M.tail_ne_shift hl') hχ h
  have h2 := M.core_step (M.tail_ne_shift hl) hχ.symm h.symm
  have ha : (lead l).1 = (lead l').1 := by omega
  have hb : (lead l).2 = (lead l').2 := by omega
  refine ⟨Prod.ext ha hb, M.shift_injective ?_⟩
  rw [ha, hb] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem eq_nil_of_val_eq_one : ∀ l : List (ℕ × ℕ), IsNF l → M.val l = 1 → l = []
  | [], _, _ => rfl
  | e :: r, hl, h => by
    obtain ⟨h1, h2⟩ := M.lead_eq_of_val_eq (l' := []) hl trivial h
    have h2' : M.val r = 1 := h2
    have hr : r = [] := eq_nil_of_val_eq_one r hl.1 h2'
    exact absurd h1 (hl.2.1 hr)

/-- **Uniqueness of the normal form.** -/
theorem nf_unique : ∀ l l' : List (ℕ × ℕ), IsNF l → IsNF l' → M.val l = M.val l' → l = l'
  | [], l', _, hl', h => (M.eq_nil_of_val_eq_one l' hl' h.symm).symm
  | _ :: _, [], hl, _, h => M.eq_nil_of_val_eq_one _ hl h
  | e :: r, e' :: r', hl, hl', h => by
    obtain ⟨h1, h2⟩ := M.lead_eq_of_val_eq hl hl' h
    have h2' : M.val r = M.val r' := h2
    have h1' : e = e' := h1
    rw [nf_unique r r' hl.1 hl'.1 h2', h1']

end FModel

end GroupApproximation.ThompsonOre
