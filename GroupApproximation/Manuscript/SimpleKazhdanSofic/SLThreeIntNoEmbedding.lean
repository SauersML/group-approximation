import GroupApproximation.Manuscript.SimpleKazhdanSofic.SiteDegreeFiniteOrder
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Setting
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# `SL₃(ℤ)` lies in no `G_X`

`simple_kazhdan_sofic_group.tex` at 696c4b602, "LEF groups" (l.482 and l.491–493):

> The groups $G_X$ do not suffice here: $\SL_3(\Z)$ lies in no $G_X$. …
> In the Heisenberg subgroup of $\SL_3(\Z)$, $[a,b]$ has infinite order and
> $[a,b]^{n^2}=[a^n,b^n]$.

* The Heisenberg generators `a = e₁₂(1)`, `b = e₂₃(1)` and `c = e₁₃(1)` in `SL₃(ℤ)` satisfy
  `aⁿ bⁿ = c^{n²} bⁿ aⁿ` (`sl_rel`). So `c = [a, b]` and `c^{n²} = [aⁿ, bⁿ]` (`slC_pow_eq`), and
  `c` has infinite order (`not_isOfFinOrder_slC`).
* For a homomorphism `φ : SL₃(ℤ) → GL_m(LC(X, F₂) ⋊ ℤ)`, let `W` bound the displacements of
  `φ(a^{±1})` and `φ(b^{±1})`. Writing `n = s² + r` with `r ≤ 2s`, the element
  `φ(c)ⁿ = [φ(a)^s, φ(b)^s] φ(c)^r` moves site vectors at most `(s + r) W ≤ 3 s W` levels
  (`hasDisplacement_slC_pow`). For `N = K²` with `K = 6mW + m + 1`, every `n < N` has `s < K`,
  and `m(2·3KW + 1) < N`. So `φ(c)` has finite order (`isOfFinOrder_of_hasDisplacement`), and
  `φ` is not injective (`not_injective_slThree_units`). Restricting to the elementary subgroup
  gives `G_X` (`not_injective_slThree_elementaryGroup`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SiteAction

open SymbolicDynamics.FullShift
open scoped commutatorElement

/-- `e₁₂(n)`. -/
def heisA (n : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, n, 0; 0, 1, 0; 0, 0, 1]

/-- `e₂₃(n)`. -/
def heisB (n : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, n; 0, 0, 1]

/-- `e₁₃(n)`. -/
def heisC (n : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, n; 0, 1, 0; 0, 0, 1]

theorem heisA_mul (n p : ℤ) : heisA n * heisA p = heisA (n + p) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisA, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem heisB_mul (n p : ℤ) : heisB n * heisB p = heisB (n + p) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisB, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem heisC_mul (n p : ℤ) : heisC n * heisC p = heisC (n + p) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisC, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

/-- **The Heisenberg relation** `aⁿ bⁿ = c^{n²} bⁿ aⁿ`. -/
theorem heis_rel (n : ℤ) : heisA n * heisB n = heisC (n * n) * heisB n * heisA n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisA, heisB, heisC, Matrix.mul_apply, Fin.sum_univ_three]

/-- `a = e₁₂(1)`. -/
def slA : Matrix.SpecialLinearGroup (Fin 3) ℤ :=
  ⟨heisA 1, by simp [heisA, Matrix.det_fin_three]⟩

/-- `b = e₂₃(1)`. -/
def slB : Matrix.SpecialLinearGroup (Fin 3) ℤ :=
  ⟨heisB 1, by simp [heisB, Matrix.det_fin_three]⟩

/-- `c = e₁₃(1)`. -/
def slC : Matrix.SpecialLinearGroup (Fin 3) ℤ :=
  ⟨heisC 1, by simp [heisC, Matrix.det_fin_three]⟩

theorem slA_pow (n : ℕ) :
    ((slA ^ n : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = heisA n := by
  induction n with
  | zero => simp [heisA, Matrix.one_fin_three]
  | succ n ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
      show heisA (n : ℤ) * heisA 1 = heisA ((n + 1 : ℕ) : ℤ)
      rw [heisA_mul, Nat.cast_succ]

theorem slB_pow (n : ℕ) :
    ((slB ^ n : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = heisB n := by
  induction n with
  | zero => simp [heisB, Matrix.one_fin_three]
  | succ n ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
      show heisB (n : ℤ) * heisB 1 = heisB ((n + 1 : ℕ) : ℤ)
      rw [heisB_mul, Nat.cast_succ]

theorem slC_pow (n : ℕ) :
    ((slC ^ n : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = heisC n := by
  induction n with
  | zero => simp [heisC, Matrix.one_fin_three]
  | succ n ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
      show heisC (n : ℤ) * heisC 1 = heisC ((n + 1 : ℕ) : ℤ)
      rw [heisC_mul, Nat.cast_succ]

theorem sl_rel (s : ℕ) : slA ^ s * slB ^ s = slC ^ (s * s) * slB ^ s * slA ^ s := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, slA_pow, slB_pow, slC_pow, Nat.cast_mul]
  exact heis_rel s

/-- `c^{s²} = [a^s, b^s]`. -/
theorem slC_pow_eq (s : ℕ) :
    slC ^ (s * s) = slA ^ s * slB ^ s * (slA ^ s)⁻¹ * (slB ^ s)⁻¹ := by
  have h := sl_rel s
  rw [mul_assoc (slC ^ (s * s))] at h
  rw [mul_assoc (slA ^ s * slB ^ s), ← mul_inv_rev, eq_mul_inv_iff_mul_eq, h]

/-- `c = [a, b]`. -/
theorem slC_eq : slC = slA * slB * slA⁻¹ * slB⁻¹ := by
  simpa using slC_pow_eq 1

/-- `[a, b]` has infinite order. -/
theorem not_isOfFinOrder_slC : ¬ IsOfFinOrder slC := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨k, hk, hpow⟩
  have h := congrArg
    (fun M : Matrix.SpecialLinearGroup (Fin 3) ℤ => (M : Matrix (Fin 3) (Fin 3) ℤ) 0 2) hpow
  simp only [slC_pow, Matrix.SpecialLinearGroup.coe_one] at h
  simp [heisC] at h
  omega

section Units

variable {Z : Type*} [TopologicalSpace Z] {T : Z ≃ₜ Z} {m : ℕ}

theorem rhoMat_units_mul (u v : (Mat2 T m)ˣ) :
    rhoMat T (ZMod 2) m ((u * v : (Mat2 T m)ˣ) : Mat2 T m) =
      rhoMat T (ZMod 2) m (u : Mat2 T m) * rhoMat T (ZMod 2) m (v : Mat2 T m) := by
  rw [Units.val_mul, map_mul]

theorem rhoMat_units_pow (u : (Mat2 T m)ˣ) (n : ℕ) :
    rhoMat T (ZMod 2) m ((u ^ n : (Mat2 T m)ˣ) : Mat2 T m) =
      rhoMat T (ZMod 2) m (u : Mat2 T m) ^ n := by
  rw [Units.val_pow_eq_pow_val, map_pow]

/-- The displacement bound for `φ(c)ⁿ`, with `n = s² + r`. -/
theorem hasDisplacement_slC_pow (φ : Matrix.SpecialLinearGroup (Fin 3) ℤ →* (Mat2 T m)ˣ)
    {wa wb wa' wb' : ℕ}
    (ha : HasDisplacement wa (rhoMat T (ZMod 2) m ((φ slA : (Mat2 T m)ˣ) : Mat2 T m)))
    (hb : HasDisplacement wb (rhoMat T (ZMod 2) m ((φ slB : (Mat2 T m)ˣ) : Mat2 T m)))
    (ha' : HasDisplacement wa' (rhoMat T (ZMod 2) m ((φ slA⁻¹ : (Mat2 T m)ˣ) : Mat2 T m)))
    (hb' : HasDisplacement wb' (rhoMat T (ZMod 2) m ((φ slB⁻¹ : (Mat2 T m)ˣ) : Mat2 T m)))
    (n : ℕ) :
    HasDisplacement (Nat.sqrt n * (wa + wb + wa' + wb') +
        (n - Nat.sqrt n * Nat.sqrt n) * (wa + wb + wa' + wb'))
      (rhoMat T (ZMod 2) m ((φ slC ^ n : (Mat2 T m)ˣ) : Mat2 T m)) := by
  have hcW : HasDisplacement (wa + wb + wa' + wb')
      (rhoMat T (ZMod 2) m ((φ slC : (Mat2 T m)ˣ) : Mat2 T m)) := by
    have e : φ slC = φ slA * φ slB * φ slA⁻¹ * φ slB⁻¹ := by
      rw [slC_eq, map_mul, map_mul, map_mul]
    rw [e, rhoMat_units_mul, rhoMat_units_mul, rhoMat_units_mul]
    exact ((ha.mul hb).mul ha').mul hb'
  have hsq : ∀ s : ℕ, HasDisplacement (s * (wa + wb + wa' + wb'))
      (rhoMat T (ZMod 2) m ((φ slC ^ (s * s) : (Mat2 T m)ˣ) : Mat2 T m)) := by
    intro s
    have e : φ slC ^ (s * s) = φ slA ^ s * φ slB ^ s * φ slA⁻¹ ^ s * φ slB⁻¹ ^ s := by
      rw [← map_pow, slC_pow_eq, map_mul, map_mul, map_mul, map_pow, map_pow, ← inv_pow,
        ← inv_pow, map_pow, map_pow]
    rw [e, rhoMat_units_mul, rhoMat_units_mul, rhoMat_units_mul, rhoMat_units_pow,
      rhoMat_units_pow, rhoMat_units_pow, rhoMat_units_pow]
    exact ((((ha.pow s).mul (hb.pow s)).mul (ha'.pow s)).mul (hb'.pow s)).mono
      (le_of_eq (by ring))
  have hs : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have e : φ slC ^ n =
      φ slC ^ (Nat.sqrt n * Nat.sqrt n) * φ slC ^ (n - Nat.sqrt n * Nat.sqrt n) := by
    rw [← pow_add, Nat.add_sub_of_le hs]
  rw [e, rhoMat_units_mul, rhoMat_units_pow (φ slC) (n - Nat.sqrt n * Nat.sqrt n)]
  exact (hsq (Nat.sqrt n)).mul (hcW.pow _)

/-- **`SL₃(ℤ)` embeds in no `GL_m(LC(X, F₂) ⋊ ℤ)`** (tex l.482–493). -/
theorem not_injective_slThree_units (φ : Matrix.SpecialLinearGroup (Fin 3) ℤ →* (Mat2 T m)ˣ) :
    ¬ Function.Injective φ := by
  intro hφ
  obtain ⟨wa, ha⟩ := exists_hasDisplacement (T := T) (m := m) ((φ slA : (Mat2 T m)ˣ) : Mat2 T m)
  obtain ⟨wb, hb⟩ := exists_hasDisplacement (T := T) (m := m) ((φ slB : (Mat2 T m)ˣ) : Mat2 T m)
  obtain ⟨wa', ha'⟩ :=
    exists_hasDisplacement (T := T) (m := m) ((φ slA⁻¹ : (Mat2 T m)ˣ) : Mat2 T m)
  obtain ⟨wb', hb'⟩ :=
    exists_hasDisplacement (T := T) (m := m) ((φ slB⁻¹ : (Mat2 T m)ˣ) : Mat2 T m)
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = wa + wb + wa' + wb' := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = 6 * m * W + m + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by
    rw [hKdef]
    exact Nat.succ_pos _
  have hfin : IsOfFinOrder (φ slC) := by
    refine isOfFinOrder_of_hasDisplacement (φ slC) (N := K * K) (D := 3 * K * W)
      (fun n hn => ?_) ?_
    · have h := hasDisplacement_slC_pow φ ha hb ha' hb' n
      rw [← hW] at h
      refine h.mono ?_
      have hs : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
      have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
      have hexp : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) =
          Nat.sqrt n * Nat.sqrt n + 2 * Nat.sqrt n + 1 := by ring
      have hsK : Nat.sqrt n < K := by
        by_contra hcon
        have hKK : K * K ≤ Nat.sqrt n * Nat.sqrt n :=
          Nat.mul_le_mul (not_lt.1 hcon) (not_lt.1 hcon)
        generalize K * K = kk at hKK hn
        generalize Nat.sqrt n * Nat.sqrt n = q at hKK hs
        omega
      have hsum : Nat.sqrt n + (n - Nat.sqrt n * Nat.sqrt n) ≤ 3 * K := by
        generalize (Nat.sqrt n + 1) * (Nat.sqrt n + 1) = pp at hlt hexp
        generalize Nat.sqrt n * Nat.sqrt n = q at hs hexp ⊢
        omega
      calc Nat.sqrt n * W + (n - Nat.sqrt n * Nat.sqrt n) * W
          = (Nat.sqrt n + (n - Nat.sqrt n * Nat.sqrt n)) * W := by ring
        _ ≤ 3 * K * W := Nat.mul_le_mul_right W hsum
    · have hKK : K * K = 6 * m * W * K + m * K + K := by
        rw [hKdef]
        ring
      have h1 : m ≤ m * K := Nat.le_mul_of_pos_right m hK0
      have e : m * (2 * (3 * K * W) + 1) = 6 * m * W * K + m := by ring
      rw [e, hKK]
      generalize 6 * m * W * K = z
      generalize m * K = y at h1 ⊢
      omega
  apply not_isOfFinOrder_slC
  obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, hφ (by rw [map_pow, hpow, map_one])⟩

end Units

/-- **`SL₃(ℤ)` lies in no `G_X`** (tex l.482): no injective homomorphism into `EL₃(R_X)`. -/
theorem not_injective_slThree_elementaryGroup {A : Type} [TopologicalSpace A] (S : Subshift A ℤ)
    (φ : Matrix.SpecialLinearGroup (Fin 3) ℤ →* G S) : ¬ Function.Injective φ := fun hφ =>
  not_injective_slThree_units (T := subshiftHomeo S) (m := 3) ((Subgroup.subtype _).comp φ)
    (Subtype.val_injective.comp hφ)

/-! ## The printed sentences -/

/-- **tex l.482**: `SL₃(ℤ)` lies in no `G_X`. The carrier covers every subshift and, more
generally, every `GL_m(LC(X, F₂) ⋊_T ℤ)`. -/
def PrintedSLThreeIntInNoGX : Prop :=
  (∀ (A : Type) [TopologicalSpace A] (S : Subshift A ℤ)
      (φ : Matrix.SpecialLinearGroup (Fin 3) ℤ →* G S), ¬ Function.Injective φ) ∧
    ∀ (Z : Type) [TopologicalSpace Z] (T : Z ≃ₜ Z) (m : ℕ)
      (φ : Matrix.SpecialLinearGroup (Fin 3) ℤ →* (Mat2 T m)ˣ), ¬ Function.Injective φ

theorem printedSLThreeIntInNoGX : PrintedSLThreeIntInNoGX :=
  ⟨fun _ _ S φ => not_injective_slThree_elementaryGroup S φ,
    fun _ _ _ _ φ => not_injective_slThree_units φ⟩

/-- **tex l.491–493**: in the Heisenberg subgroup of `SL₃(ℤ)`, `[a, b]` has infinite order and
`[a, b]^{n²} = [aⁿ, bⁿ]`. -/
def PrintedHeisenbergDistortion : Prop :=
  ¬ IsOfFinOrder ⁅slA, slB⁆ ∧ ∀ n : ℕ, ⁅slA, slB⁆ ^ (n ^ 2) = ⁅slA ^ n, slB ^ n⁆

theorem printedHeisenbergDistortion : PrintedHeisenbergDistortion := by
  refine ⟨?_, fun n => ?_⟩
  · rw [commutatorElement_def, ← slC_eq]
    exact not_isOfFinOrder_slC
  · rw [commutatorElement_def, commutatorElement_def, ← slC_eq, pow_two, slC_pow_eq]

#audit_closed_axioms printedSLThreeIntInNoGX
#audit_closed_axioms printedHeisenbergDistortion

end SiteAction
end SimpleKazhdanSofic
end GroupApproximation
