import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.LinearCombination
import GroupApproximation.GroupTheory.HigmanThompson.GeometricF
import GroupApproximation.Meta.AxiomGuard

/-!
# Moves in the Higman–Thompson groups

Hyde–Lodha's simplicity argument moves finitely many points of `ℤ[1/n]` around by elements
of `F_n`.  This module builds those elements explicitly, for `n = m + 2`, as products of affine
charts and powers of Brown's generator `x_0`, so that membership in `PLGroup n (n^ℤ)` is
automatic and only point values need computing.

* `ResEq m x y`: `x - y ∈ (n - 1) ℤ[1/n]`, the residue that `F_n` preserves.
* `psiPerm m N t a = A⁻¹ x_0^t A` with `A t = n^N (t - a)`: the identity on `(-∞, a]`,
  translation by `t (n-1) n^{-N}` on `[a + n^{-N}, ∞)`, and slope `n` on `[a, a + n^{-N}]` when
  `t = 1`.
* `movePerm m N t α β = T⁻¹ ψ_{β - n^{-N}} T ψ_α⁻¹`, `T` the translation by `d = t (n-1) n^{-N}`:
  the identity off `(α, β)`, sending `x` to `x - d`.  `exists_move`: for points `α < x, y < β`
  of `ℤ[1/n]` with `ResEq m x y` there is an element of `PLGroup` fixing `(-∞, α]` and
  `[β, ∞)` and sending `x` to `y`.
* `germLeft`, `germRight`: elements with slope `n` at `0⁺` (resp. `1⁻`) supported in `[0, ζ]`
  (resp. `[1 - ζ, 1]`).
-/

namespace GroupApproximation
namespace HigmanThompson

/-! ## Residues -/

section Residues

variable (m : ℕ)

/-- `x ≡ y` modulo `(n - 1) ℤ[1/n]`, `n = m + 2`. -/
def ResEq (x y : ℚ) : Prop :=
  ∃ N : ℕ, ∃ k : ℤ, (x - y) * ((m : ℚ) + 2) ^ N = ((m : ℚ) + 1) * k

variable {m}

theorem ResEq.refl (x : ℚ) : ResEq m x x := ⟨0, 0, by simp⟩

theorem ResEq.symm {x y : ℚ} (h : ResEq m x y) : ResEq m y x := by
  obtain ⟨N, k, hk⟩ := h
  refine ⟨N, -k, ?_⟩
  push_cast
  linear_combination -hk

theorem ResEq.trans {x y z : ℚ} (h₁ : ResEq m x y) (h₂ : ResEq m y z) : ResEq m x z := by
  obtain ⟨N₁, k₁, hk₁⟩ := h₁
  obtain ⟨N₂, k₂, hk₂⟩ := h₂
  refine ⟨N₁ + N₂, k₁ * ((m : ℤ) + 2) ^ N₂ + k₂ * ((m : ℤ) + 2) ^ N₁, ?_⟩
  push_cast
  rw [pow_add]
  linear_combination ((m : ℚ) + 2) ^ N₂ * hk₁ + ((m : ℚ) + 2) ^ N₁ * hk₂

/-- A residue relation holds at every finer level. -/
theorem resEq_level {x y : ℚ} {N₀ : ℕ} {k : ℤ}
    (hk : (x - y) * ((m : ℚ) + 2) ^ N₀ = ((m : ℚ) + 1) * k) {N : ℕ} (hN : N₀ ≤ N) :
    ∃ k' : ℤ, (x - y) * ((m : ℚ) + 2) ^ N = ((m : ℚ) + 1) * k' := by
  refine ⟨k * ((m : ℤ) + 2) ^ (N - N₀), ?_⟩
  have e : ((m : ℚ) + 2) ^ N = ((m : ℚ) + 2) ^ N₀ * ((m : ℚ) + 2) ^ (N - N₀) := by
    rw [← pow_add, Nat.add_sub_of_le hN]
  push_cast
  rw [e]
  linear_combination ((m : ℚ) + 2) ^ (N - N₀) * hk

/-- Some level `N ≥ M` has `n^{-N} ≤ δ`. -/
theorem exists_level (M : ℕ) {δ : ℚ} (hδ : 0 < δ) :
    ∃ N : ℕ, M ≤ N ∧ (((m : ℚ) + 2) ^ N)⁻¹ ≤ δ := by
  obtain ⟨K, hK⟩ := exists_nat_gt δ⁻¹
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hpow : ∀ j : ℕ, (j : ℚ) + 1 ≤ ((m : ℚ) + 2) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
      rw [pow_succ]
      push_cast
      nlinarith
  refine ⟨max M K, le_max_left M K, ?_⟩
  have hp1 : (1 : ℚ) ≤ (m : ℚ) + 2 := by linarith
  have hKN : (K : ℚ) ≤ ((m : ℚ) + 2) ^ (max M K) := by
    have h1 := hpow K
    have h2 : ((m : ℚ) + 2) ^ K ≤ ((m : ℚ) + 2) ^ (max M K) :=
      pow_le_pow_right₀ hp1 (le_max_right M K)
    linarith
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ (max M K) := pow_pos mTwo_pos _
  have h1 : 1 < δ * K := by
    have h := mul_lt_mul_of_pos_left hK hδ
    rwa [mul_inv_cancel₀ hδ.ne'] at h
  have h2 : 1 ≤ δ * ((m : ℚ) + 2) ^ (max M K) := by
    have h := mul_le_mul_of_nonneg_left hKN hδ.le
    linarith
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  linarith

end Residues

/-! ## Affine charts -/

section Charts

variable (m : ℕ)

/-- Translation `t ↦ t + c`. -/
def transPerm (c : ℚ) : Equiv.Perm ℚ where
  toFun t := t + c
  invFun t := t - c
  left_inv t := by simp
  right_inv t := by simp

@[simp] theorem transPerm_apply (c t : ℚ) : transPerm c t = t + c := rfl

theorem transPerm_inv_apply (c t : ℚ) : (transPerm c)⁻¹ t = t - c := rfl

/-- The chart `t ↦ n^N (t - a)`. -/
def scalePerm (N : ℕ) (a : ℚ) : Equiv.Perm ℚ where
  toFun t := ((m : ℚ) + 2) ^ N * (t - a)
  invFun t := a + t * (((m : ℚ) + 2) ^ N)⁻¹
  left_inv t := by
    have h : ((m : ℚ) + 2) ^ N ≠ 0 := pow_ne_zero N mTwo_pos.ne'
    have hinv : ((m : ℚ) + 2) ^ N * (((m : ℚ) + 2) ^ N)⁻¹ = 1 := mul_inv_cancel₀ h
    show a + ((m : ℚ) + 2) ^ N * (t - a) * (((m : ℚ) + 2) ^ N)⁻¹ = t
    linear_combination (t - a) * hinv
  right_inv t := by
    have h : ((m : ℚ) + 2) ^ N ≠ 0 := pow_ne_zero N mTwo_pos.ne'
    have hinv : ((m : ℚ) + 2) ^ N * (((m : ℚ) + 2) ^ N)⁻¹ = 1 := mul_inv_cancel₀ h
    show ((m : ℚ) + 2) ^ N * (a + t * (((m : ℚ) + 2) ^ N)⁻¹ - a) = t
    linear_combination t * hinv

@[simp] theorem scalePerm_apply (N : ℕ) (a t : ℚ) :
    scalePerm m N a t = ((m : ℚ) + 2) ^ N * (t - a) := rfl

theorem scalePerm_inv_apply (N : ℕ) (a t : ℚ) :
    (scalePerm m N a)⁻¹ t = a + t * (((m : ℚ) + 2) ^ N)⁻¹ := rfl

theorem perm_inv_eq_of_apply_eq {f : Equiv.Perm ℚ} {u w : ℚ} (h : f u = w) : f⁻¹ w = u :=
  Equiv.Perm.inv_eq_iff_eq.mpr h.symm

theorem powSlopes_natPow (N : ℕ) : ((m : ℚ) + 2) ^ N ∈ powSlopes m :=
  ⟨N, by rw [zpow_natCast]⟩

theorem powSlopes_natPow_inv (N : ℕ) : (((m : ℚ) + 2) ^ N)⁻¹ ∈ powSlopes m :=
  ⟨-(N : ℤ), by rw [zpow_neg, zpow_natCast]⟩

theorem mTwoPow_inv_mem_grid (N : ℕ) : (((m : ℚ) + 2) ^ N)⁻¹ ∈ Grid (m + 2) N := by
  refine ⟨1, ?_⟩
  push_cast
  exact inv_mul_cancel₀ (pow_ne_zero N mTwo_pos.ne')

theorem one_mem_grid_mTwo (M : ℕ) : (1 : ℚ) ∈ Grid (m + 2) M := by
  simpa using int_mem_grid (m := m + 2) M 1

theorem transPerm_gridAffine {c : ℚ} {M : ℕ} (hc : c ∈ Grid (m + 2) M) :
    GridAffine (m + 2) (powSlopes m) ⇑(transPerm c) 0 M := by
  have e : ⇑(transPerm c) = fun t => 1 * t + c := by
    funext t
    show t + c = 1 * t + c
    ring
  rw [e]
  exact gridAffine_affine (powSlopes m).one_mem (one_mem_grid_mTwo m M) hc

theorem transPerm_inv_gridAffine {c : ℚ} {M : ℕ} (hc : c ∈ Grid (m + 2) M) :
    GridAffine (m + 2) (powSlopes m) ⇑(transPerm c)⁻¹ 0 M := by
  have e : ⇑(transPerm c)⁻¹ = fun t => 1 * t + -c := by
    funext t
    show t - c = 1 * t + -c
    ring
  rw [e]
  exact gridAffine_affine (powSlopes m).one_mem (one_mem_grid_mTwo m M) (grid_neg hc)

theorem transPerm_mem {c : ℚ} {M : ℕ} (hc : c ∈ Grid (m + 2) M) :
    transPerm c ∈ PLGroup (m + 2) (powSlopes m) := by
  refine ⟨fun s t hst => ?_, ⟨0, M, transPerm_gridAffine m hc⟩,
    ⟨0, M, transPerm_inv_gridAffine m hc⟩⟩
  show s + c < t + c
  linarith

theorem scalePerm_gridAffine (N : ℕ) {a : ℚ} (ha : a ∈ Grid (m + 2) N) :
    GridAffine (m + 2) (powSlopes m) ⇑(scalePerm m N a) 0 0 := by
  have e : ⇑(scalePerm m N a) =
      fun t => ((m : ℚ) + 2) ^ N * t + -(((m : ℚ) + 2) ^ N * a) := by
    funext t
    show ((m : ℚ) + 2) ^ N * (t - a) = ((m : ℚ) + 2) ^ N * t + -(((m : ℚ) + 2) ^ N * a)
    ring
  rw [e]
  refine gridAffine_affine (powSlopes_natPow m N) ⟨((m : ℤ) + 2) ^ N, by push_cast; ring⟩ ?_
  obtain ⟨k, hk⟩ := ha
  refine ⟨-k, ?_⟩
  push_cast at hk ⊢
  linear_combination -hk

theorem scalePerm_inv_gridAffine (N : ℕ) {a : ℚ} (ha : a ∈ Grid (m + 2) N) :
    GridAffine (m + 2) (powSlopes m) ⇑(scalePerm m N a)⁻¹ 0 N := by
  have e : ⇑(scalePerm m N a)⁻¹ = fun t => (((m : ℚ) + 2) ^ N)⁻¹ * t + a := by
    funext t
    show a + t * (((m : ℚ) + 2) ^ N)⁻¹ = (((m : ℚ) + 2) ^ N)⁻¹ * t + a
    ring
  rw [e]
  exact gridAffine_affine (powSlopes_natPow_inv m N) (mTwoPow_inv_mem_grid m N) ha

theorem scalePerm_mem (N : ℕ) {a : ℚ} (ha : a ∈ Grid (m + 2) N) :
    scalePerm m N a ∈ PLGroup (m + 2) (powSlopes m) := by
  refine ⟨fun s t hst => ?_, ⟨0, 0, scalePerm_gridAffine m N ha⟩,
    ⟨0, N, scalePerm_inv_gridAffine m N ha⟩⟩
  show ((m : ℚ) + 2) ^ N * (s - a) < ((m : ℚ) + 2) ^ N * (t - a)
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hst a) (pow_pos mTwo_pos N)

end Charts

/-! ## Powers of `x_0` -/

section Powers

variable (m : ℕ)

theorem xg_zero_pow_of_nonpos (t : ℕ) {s : ℚ} (hs : s ≤ 0) : (xg m 0 ^ t) s = s := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, Equiv.Perm.mul_apply, xg_fix (k := 0) (t := s) (by simpa using hs), ih]

theorem xg_zero_pow_of_one_le (t : ℕ) {s : ℚ} (hs : 1 ≤ s) :
    (xg m 0 ^ t) s = s + t * ((m : ℚ) + 1) := by
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, xg_apply, xfun_of_ge (k := 0) (t := s) (by simpa using hs),
      ih (s := s + ((m : ℚ) + 1)) (by linarith)]
    push_cast
    ring

/-- `ψ_a = A_a⁻¹ x_0^t A_a`. -/
noncomputable def psiPerm (N t : ℕ) (a : ℚ) : Equiv.Perm ℚ :=
  (scalePerm m N a)⁻¹ * xg m 0 ^ t * scalePerm m N a

theorem psiPerm_mem (N t : ℕ) {a : ℚ} (ha : a ∈ Grid (m + 2) N) :
    psiPerm m N t a ∈ PLGroup (m + 2) (powSlopes m) :=
  (PLGroup (m + 2) (powSlopes m)).mul_mem
    ((PLGroup (m + 2) (powSlopes m)).mul_mem
      ((PLGroup (m + 2) (powSlopes m)).inv_mem (scalePerm_mem m N ha))
      ((PLGroup (m + 2) (powSlopes m)).pow_mem (xg_mem_geoF m 0).1 t))
    (scalePerm_mem m N ha)

theorem psiPerm_of_le (N t : ℕ) {a u : ℚ} (hu : u ≤ a) : psiPerm m N t a u = u := by
  have h0 : scalePerm m N a u ≤ 0 := by
    show ((m : ℚ) + 2) ^ N * (u - a) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos (pow_pos mTwo_pos N).le (sub_nonpos.mpr hu)
  simp only [psiPerm, Equiv.Perm.mul_apply]
  rw [xg_zero_pow_of_nonpos m t h0]
  exact Equiv.symm_apply_apply (scalePerm m N a) u

theorem psiPerm_of_ge (N t : ℕ) {a u : ℚ} (hu : a + (((m : ℚ) + 2) ^ N)⁻¹ ≤ u) :
    psiPerm m N t a u = u + t * ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ N)⁻¹ := by
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ N := pow_pos mTwo_pos N
  have hinv : ((m : ℚ) + 2) ^ N * (((m : ℚ) + 2) ^ N)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have h1 : 1 ≤ scalePerm m N a u := by
    show 1 ≤ ((m : ℚ) + 2) ^ N * (u - a)
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_right hu a) hpos.le
    have e : ((m : ℚ) + 2) ^ N * (a + (((m : ℚ) + 2) ^ N)⁻¹ - a) = 1 := by
      linear_combination hinv
    linarith
  simp only [psiPerm, Equiv.Perm.mul_apply]
  rw [xg_zero_pow_of_one_le m t h1, scalePerm_inv_apply, scalePerm_apply]
  linear_combination (u - a) * hinv

theorem psiPerm_one_of_mem (N : ℕ) {a u : ℚ} (hu1 : a ≤ u)
    (hu2 : u ≤ a + (((m : ℚ) + 2) ^ N)⁻¹) :
    psiPerm m N 1 a u = a + ((m : ℚ) + 2) * (u - a) := by
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ N := pow_pos mTwo_pos N
  have hinv : ((m : ℚ) + 2) ^ N * (((m : ℚ) + 2) ^ N)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have h0 : ((0 : ℕ) : ℚ) ≤ scalePerm m N a u := by
    show ((0 : ℕ) : ℚ) ≤ ((m : ℚ) + 2) ^ N * (u - a)
    push_cast
    exact mul_nonneg hpos.le (sub_nonneg.mpr hu1)
  have h1 : scalePerm m N a u ≤ ((0 : ℕ) : ℚ) + 1 := by
    show ((m : ℚ) + 2) ^ N * (u - a) ≤ ((0 : ℕ) : ℚ) + 1
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_right hu2 a) hpos.le
    have e : ((m : ℚ) + 2) ^ N * (a + (((m : ℚ) + 2) ^ N)⁻¹ - a) = 1 := by
      linear_combination hinv
    push_cast
    linarith
  simp only [psiPerm, Equiv.Perm.mul_apply, pow_one]
  rw [xg_apply, xfun_of_mem h0 h1, scalePerm_inv_apply, scalePerm_apply]
  push_cast
  linear_combination ((m : ℚ) + 2) * (u - a) * hinv

end Powers

/-! ## Moves -/

section Moves

variable (m : ℕ)

/-- The displacement `t (n - 1) n^{-N}` of a move. -/
def moveStep (N t : ℕ) : ℚ := t * ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ N)⁻¹

/-- **A move**: `T⁻¹ ψ_{β - n^{-N}} T ψ_α⁻¹`, with `T` the translation by `moveStep m N t`. -/
noncomputable def movePerm (N t : ℕ) (α β : ℚ) : Equiv.Perm ℚ :=
  (transPerm (moveStep m N t))⁻¹ * psiPerm m N t (β - (((m : ℚ) + 2) ^ N)⁻¹) *
    transPerm (moveStep m N t) * (psiPerm m N t α)⁻¹

theorem moveStep_mem_grid (N t : ℕ) : moveStep m N t ∈ Grid (m + 2) N := by
  refine ⟨t * ((m : ℤ) + 1), ?_⟩
  have hinv : (((m : ℚ) + 2) ^ N)⁻¹ * ((m : ℚ) + 2) ^ N = 1 :=
    inv_mul_cancel₀ (pow_ne_zero N mTwo_pos.ne')
  unfold moveStep
  push_cast
  linear_combination (t : ℚ) * ((m : ℚ) + 1) * hinv

theorem movePerm_mem (N t : ℕ) {α β : ℚ} (hα : α ∈ Grid (m + 2) N)
    (hβ : β ∈ Grid (m + 2) N) : movePerm m N t α β ∈ PLGroup (m + 2) (powSlopes m) := by
  have hT := transPerm_mem m (moveStep_mem_grid m N t)
  have hb : β - (((m : ℚ) + 2) ^ N)⁻¹ ∈ Grid (m + 2) N := grid_sub hβ (mTwoPow_inv_mem_grid m N)
  have hψb := psiPerm_mem m N t hb
  have hψα := psiPerm_mem m N t hα
  exact (PLGroup (m + 2) (powSlopes m)).mul_mem
    ((PLGroup (m + 2) (powSlopes m)).mul_mem
      ((PLGroup (m + 2) (powSlopes m)).mul_mem ((PLGroup (m + 2) (powSlopes m)).inv_mem hT) hψb)
      hT)
    ((PLGroup (m + 2) (powSlopes m)).inv_mem hψα)

theorem movePerm_of_le (N t : ℕ) {α β u : ℚ}
    (hC : α + moveStep m N t + (((m : ℚ) + 2) ^ N)⁻¹ ≤ β) (hu : u ≤ α) :
    movePerm m N t α β u = u := by
  have h1 : (psiPerm m N t α)⁻¹ u = u := perm_inv_eq_of_apply_eq (psiPerm_of_le m N t hu)
  have h2 : psiPerm m N t (β - (((m : ℚ) + 2) ^ N)⁻¹) (u + moveStep m N t) =
      u + moveStep m N t :=
    psiPerm_of_le m N t (by linarith)
  simp only [movePerm, Equiv.Perm.mul_apply]
  rw [h1, transPerm_apply, h2, transPerm_inv_apply]
  ring

theorem movePerm_of_ge (N t : ℕ) {α β u : ℚ}
    (hC : α + moveStep m N t + (((m : ℚ) + 2) ^ N)⁻¹ ≤ β) (hu : β ≤ u) :
    movePerm m N t α β u = u := by
  have h1 : (psiPerm m N t α)⁻¹ u = u - moveStep m N t := by
    apply perm_inv_eq_of_apply_eq
    rw [psiPerm_of_ge m N t (a := α) (u := u - moveStep m N t) (by linarith)]
    unfold moveStep
    ring
  have h2 : psiPerm m N t (β - (((m : ℚ) + 2) ^ N)⁻¹) u = u + moveStep m N t := by
    rw [psiPerm_of_ge m N t (a := β - (((m : ℚ) + 2) ^ N)⁻¹) (u := u) (by linarith)]
    rfl
  simp only [movePerm, Equiv.Perm.mul_apply]
  rw [h1, transPerm_apply, sub_add_cancel, h2, transPerm_inv_apply]
  ring

theorem movePerm_apply (N t : ℕ) {α β x : ℚ}
    (hx1 : α + (((m : ℚ) + 2) ^ N)⁻¹ + moveStep m N t ≤ x)
    (hx2 : x + (((m : ℚ) + 2) ^ N)⁻¹ ≤ β) :
    movePerm m N t α β x = x - moveStep m N t := by
  have h1 : (psiPerm m N t α)⁻¹ x = x - moveStep m N t := by
    apply perm_inv_eq_of_apply_eq
    rw [psiPerm_of_ge m N t (a := α) (u := x - moveStep m N t) (by linarith)]
    unfold moveStep
    ring
  have h2 : psiPerm m N t (β - (((m : ℚ) + 2) ^ N)⁻¹) x = x :=
    psiPerm_of_le m N t (by linarith)
  simp only [movePerm, Equiv.Perm.mul_apply]
  rw [h1, transPerm_apply, sub_add_cancel, h2, transPerm_inv_apply]

/-- A move sending the larger point `x` down to `y`. -/
theorem exists_move_of_le {α β x y : ℚ} (hα : ∃ M, α ∈ Grid (m + 2) M)
    (hβ : ∃ M, β ∈ Grid (m + 2) M) (hres : ResEq m x y) (hyx : y ≤ x) (hαy : α < y)
    (hxβ : x < β) :
    ∃ h ∈ PLGroup (m + 2) (powSlopes m),
      (∀ u, u ≤ α → h u = u) ∧ (∀ u, β ≤ u → h u = u) ∧ h x = y := by
  obtain ⟨Mα, hMα⟩ := hα
  obtain ⟨Mβ, hMβ⟩ := hβ
  obtain ⟨Nr, k, hk⟩ := hres
  have hδ : 0 < min (y - α) (β - x) := lt_min (sub_pos.mpr hαy) (sub_pos.mpr hxβ)
  obtain ⟨N, hN, hε⟩ := exists_level (m := m) (max (max Mα Mβ) Nr) hδ
  have hαN : α ∈ Grid (m + 2) N :=
    grid_mono (le_trans (le_trans (le_max_left Mα Mβ) (le_max_left _ Nr)) hN) hMα
  have hβN : β ∈ Grid (m + 2) N :=
    grid_mono (le_trans (le_trans (le_max_right Mα Mβ) (le_max_left _ Nr)) hN) hMβ
  obtain ⟨k', hk'⟩ := resEq_level hk (N := N) (le_trans (le_max_right _ Nr) hN)
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ N := pow_pos mTwo_pos N
  have hinv : ((m : ℚ) + 2) ^ N * (((m : ℚ) + 2) ^ N)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hm1 : (0 : ℚ) < (m : ℚ) + 1 := by
    have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    linarith
  have hk0 : (0 : ℚ) ≤ (k' : ℚ) := by
    have h1 : 0 ≤ (x - y) * ((m : ℚ) + 2) ^ N := mul_nonneg (sub_nonneg.mpr hyx) hpos.le
    nlinarith
  have hk0' : 0 ≤ k' := by exact_mod_cast hk0
  have hcast : ((k'.toNat : ℕ) : ℚ) = (k' : ℚ) := by
    have h := Int.toNat_of_nonneg hk0'
    exact_mod_cast h
  have hstep : moveStep m N k'.toNat = x - y := by
    unfold moveStep
    rw [hcast]
    linear_combination (-(((m : ℚ) + 2) ^ N)⁻¹) * hk' + (x - y) * hinv
  have hε1 : (((m : ℚ) + 2) ^ N)⁻¹ ≤ y - α := le_trans hε (min_le_left _ _)
  have hε2 : (((m : ℚ) + 2) ^ N)⁻¹ ≤ β - x := le_trans hε (min_le_right _ _)
  have hC : α + moveStep m N k'.toNat + (((m : ℚ) + 2) ^ N)⁻¹ ≤ β := by
    rw [hstep]
    linarith
  refine ⟨movePerm m N k'.toNat α β, movePerm_mem m N k'.toNat hαN hβN,
    fun u hu => movePerm_of_le m N k'.toNat hC hu,
    fun u hu => movePerm_of_ge m N k'.toNat hC hu, ?_⟩
  have hx1 : α + (((m : ℚ) + 2) ^ N)⁻¹ + moveStep m N k'.toNat ≤ x := by
    rw [hstep]
    linarith
  have hx2 : x + (((m : ℚ) + 2) ^ N)⁻¹ ≤ β := by linarith
  rw [movePerm_apply m N k'.toNat hx1 hx2, hstep]
  ring

/-- **Moves.**  For points `α < x, y < β` of `ℤ[1/n]` with `x ≡ y` modulo `(n-1) ℤ[1/n]`, some
element of `PLGroup n (n^ℤ)` fixes `(-∞, α]` and `[β, ∞)` and sends `x` to `y`. -/
theorem exists_move {α β x y : ℚ} (hα : ∃ M, α ∈ Grid (m + 2) M)
    (hβ : ∃ M, β ∈ Grid (m + 2) M) (hres : ResEq m x y) (hαx : α < x) (hαy : α < y)
    (hxβ : x < β) (hyβ : y < β) :
    ∃ h ∈ PLGroup (m + 2) (powSlopes m),
      (∀ u, u ≤ α → h u = u) ∧ (∀ u, β ≤ u → h u = u) ∧ h x = y := by
  rcases le_total y x with hyx | hxy
  · exact exists_move_of_le m hα hβ hres hyx hαy hxβ
  · obtain ⟨h, hmem, hlow, hhigh, hyx⟩ := exists_move_of_le m hα hβ hres.symm hxy hαx hyβ
    refine ⟨h⁻¹, (PLGroup (m + 2) (powSlopes m)).inv_mem hmem,
      fun u hu => perm_inv_eq_of_apply_eq (hlow u hu),
      fun u hu => perm_inv_eq_of_apply_eq (hhigh u hu), perm_inv_eq_of_apply_eq hyx⟩

/-! ## Germ elements -/

/-- Slope `n` at `0⁺`, supported in `[0, ζ]`. -/
noncomputable def germLeft (N : ℕ) (ζ : ℚ) : Equiv.Perm ℚ :=
  (psiPerm m N 1 (ζ - (((m : ℚ) + 2) ^ N)⁻¹))⁻¹ * psiPerm m N 1 0

/-- Slope `n` at `1⁻`, supported in `[1 - ζ, 1]`. -/
noncomputable def germRight (N : ℕ) (ζ : ℚ) : Equiv.Perm ℚ :=
  (psiPerm m N 1 (1 - ζ))⁻¹ * psiPerm m N 1 (1 - (((m : ℚ) + 2) ^ N)⁻¹)

theorem germLeft_mem (N : ℕ) {ζ : ℚ} (hζ : ζ ∈ Grid (m + 2) N) :
    germLeft m N ζ ∈ PLGroup (m + 2) (powSlopes m) :=
  (PLGroup (m + 2) (powSlopes m)).mul_mem
    ((PLGroup (m + 2) (powSlopes m)).inv_mem
      (psiPerm_mem m N 1 (grid_sub hζ (mTwoPow_inv_mem_grid m N))))
    (psiPerm_mem m N 1 (by simpa using int_mem_grid (m := m + 2) N 0))

theorem germRight_mem (N : ℕ) {ζ : ℚ} (hζ : ζ ∈ Grid (m + 2) N) :
    germRight m N ζ ∈ PLGroup (m + 2) (powSlopes m) :=
  (PLGroup (m + 2) (powSlopes m)).mul_mem
    ((PLGroup (m + 2) (powSlopes m)).inv_mem
      (psiPerm_mem m N 1 (grid_sub (one_mem_grid_mTwo m N) hζ)))
    (psiPerm_mem m N 1 (grid_sub (one_mem_grid_mTwo m N) (mTwoPow_inv_mem_grid m N)))

section GermFormulas

variable {m}

theorem germLeft_of_nonpos (N : ℕ) {ζ u : ℚ} (hζ : ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ N)⁻¹ ≤ ζ)
    (hu : u ≤ 0) : germLeft m N ζ u = u := by
  have hε : 0 ≤ (((m : ℚ) + 2) ^ N)⁻¹ := inv_nonneg.mpr (pow_pos mTwo_pos N).le
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have h1 : psiPerm m N 1 0 u = u := psiPerm_of_le m N 1 hu
  have h2 : psiPerm m N 1 (ζ - (((m : ℚ) + 2) ^ N)⁻¹) u = u :=
    psiPerm_of_le m N 1 (by nlinarith)
  simp only [germLeft, Equiv.Perm.mul_apply]
  rw [h1]
  exact perm_inv_eq_of_apply_eq h2

theorem germLeft_of_ge (N : ℕ) {ζ u : ℚ} (hζ : ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ N)⁻¹ ≤ ζ)
    (hu : ζ ≤ u) : germLeft m N ζ u = u := by
  have hε : 0 ≤ (((m : ℚ) + 2) ^ N)⁻¹ := inv_nonneg.mpr (pow_pos mTwo_pos N).le
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have h1 : psiPerm m N 1 0 u = u + ((1 : ℕ) : ℚ) * ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ N)⁻¹ :=
    psiPerm_of_ge m N 1 (by nlinarith)
  have h2 : psiPerm m N 1 (ζ - (((m : ℚ) + 2) ^ N)⁻¹) u =
      u + ((1 : ℕ) : ℚ) * ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ N)⁻¹ :=
    psiPerm_of_ge m N 1 (by linarith)
  simp only [germLeft, Equiv.Perm.mul_apply]
  rw [h1]
  exact perm_inv_eq_of_apply_eq h2

theorem germLeft_near (N : ℕ) {ζ u : ℚ} (hζ : ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ N)⁻¹ ≤ ζ)
    (hu1 : 0 ≤ u) (hu2 : u ≤ (((m : ℚ) + 2) ^ N)⁻¹) :
    germLeft m N ζ u = ((m : ℚ) + 2) * u := by
  have h1 : psiPerm m N 1 0 u = 0 + ((m : ℚ) + 2) * (u - 0) :=
    psiPerm_one_of_mem m N hu1 (by linarith)
  have h2 : psiPerm m N 1 (ζ - (((m : ℚ) + 2) ^ N)⁻¹) (((m : ℚ) + 2) * u) =
      ((m : ℚ) + 2) * u :=
    psiPerm_of_le m N 1 (by nlinarith)
  simp only [germLeft, Equiv.Perm.mul_apply]
  rw [h1, zero_add, sub_zero]
  exact perm_inv_eq_of_apply_eq h2

theorem germRight_of_le (N : ℕ) {ζ u : ℚ} (hζ : ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ N)⁻¹ ≤ ζ)
    (hu : u ≤ 1 - ζ) : germRight m N ζ u = u := by
  have hε : 0 ≤ (((m : ℚ) + 2) ^ N)⁻¹ := inv_nonneg.mpr (pow_pos mTwo_pos N).le
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have h1 : psiPerm m N 1 (1 - (((m : ℚ) + 2) ^ N)⁻¹) u = u := psiPerm_of_le m N 1 (by nlinarith)
  have h2 : psiPerm m N 1 (1 - ζ) u = u := psiPerm_of_le m N 1 hu
  simp only [germRight, Equiv.Perm.mul_apply]
  rw [h1]
  exact perm_inv_eq_of_apply_eq h2

theorem germRight_of_ge (N : ℕ) {ζ u : ℚ} (hζ : ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ N)⁻¹ ≤ ζ)
    (hu : 1 ≤ u) : germRight m N ζ u = u := by
  have hε : 0 ≤ (((m : ℚ) + 2) ^ N)⁻¹ := inv_nonneg.mpr (pow_pos mTwo_pos N).le
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have h1 : psiPerm m N 1 (1 - (((m : ℚ) + 2) ^ N)⁻¹) u =
      u + ((1 : ℕ) : ℚ) * ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ N)⁻¹ :=
    psiPerm_of_ge m N 1 (by linarith)
  have h2 : psiPerm m N 1 (1 - ζ) u = u + ((1 : ℕ) : ℚ) * ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ N)⁻¹ :=
    psiPerm_of_ge m N 1 (by nlinarith)
  simp only [germRight, Equiv.Perm.mul_apply]
  rw [h1]
  exact perm_inv_eq_of_apply_eq h2

theorem germRight_near (N : ℕ) {ζ u : ℚ} (hζ : ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ N)⁻¹ ≤ ζ)
    (hu1 : 1 - (((m : ℚ) + 2) ^ N)⁻¹ ≤ u) (hu2 : u ≤ 1) :
    germRight m N ζ u = 1 + ((m : ℚ) + 2) * (u - 1) := by
  have hε : 0 ≤ (((m : ℚ) + 2) ^ N)⁻¹ := inv_nonneg.mpr (pow_pos mTwo_pos N).le
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have h1 : psiPerm m N 1 (1 - (((m : ℚ) + 2) ^ N)⁻¹) u =
      (1 - (((m : ℚ) + 2) ^ N)⁻¹) + ((m : ℚ) + 2) * (u - (1 - (((m : ℚ) + 2) ^ N)⁻¹)) :=
    psiPerm_one_of_mem m N hu1 (by linarith)
  have h2 : psiPerm m N 1 (1 - ζ) (1 + ((m : ℚ) + 2) * (u - 1)) =
      (1 - (((m : ℚ) + 2) ^ N)⁻¹) + ((m : ℚ) + 2) * (u - (1 - (((m : ℚ) + 2) ^ N)⁻¹)) := by
    rw [psiPerm_of_ge m N 1 (a := 1 - ζ) (u := 1 + ((m : ℚ) + 2) * (u - 1)) (by nlinarith)]
    push_cast
    ring
  simp only [germRight, Equiv.Perm.mul_apply]
  rw [h1]
  exact perm_inv_eq_of_apply_eq h2

end GermFormulas

end Moves

#audit_axioms GroupApproximation.HigmanThompson.exists_move
#audit_axioms GroupApproximation.HigmanThompson.germLeft_near
#audit_axioms GroupApproximation.HigmanThompson.germRight_near

end HigmanThompson
end GroupApproximation
