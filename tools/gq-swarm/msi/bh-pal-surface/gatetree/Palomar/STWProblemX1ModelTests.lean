/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Palomar.STWProblemX1Challenge

/-!
# Model tests for the Problem X(1) challenge

Every `Prop` of `Palomar/STWProblemX1Challenge.lean` is exercised on a small instance.

* `IsCompletelyPositive`: the scalar embedding `ℂ → M_Y(ℂ)` passes, and its negative fails on a
  one-point carrier.
* `TracialState`: the identity is a tracial state on `ℂ`, every tracial state on `ℂ` is the
  identity, and no tracial state is zero.
* `normalizedTrace` and `hilbertSchmidtNorm` are normalized: both give `1` on the unit matrix.
* `IsQuasidiagonalTrace` and `IsAmenableTrace`: every tracial state on `ℂ` has both kinds of
  model, so the printed universal holds for `ℂ` and a counterexample must be larger.
* The trace clause pins the state, and it makes the matrix sizes eventually positive.

The prose of this module was written by Claude (Anthropic).
-/

namespace STWProblemX1
namespace ModelTests

open Filter
open scoped ComplexOrder Matrix.Norms.L2Operator

noncomputable section

/-! ### Tracial states -/

/-- The identity is a tracial state on `ℂ`. -/
def complexTracialState : TracialState ℂ where
  toLinearMap := LinearMap.id
  map_one := rfl
  map_star_mul_self_nonneg z := by
    have h : ((Complex.normSq z : ℝ) : ℂ) = star z * z := Complex.normSq_eq_conj_mul_self
    show (0 : ℂ) ≤ star z * z
    rw [← h]
    exact Complex.zero_le_real.2 (Complex.normSq_nonneg z)
  map_mul_comm z w := mul_comm z w

/-- The unit condition pins a tracial state on `ℂ`: it is the identity. -/
theorem tracialState_complex_apply (τ : TracialState ℂ) (z : ℂ) : τ.toLinearMap z = z := by
  have h := map_smul τ.toLinearMap z (1 : ℂ)
  simp only [smul_eq_mul, mul_one, τ.map_one] at h
  exact h

/-- No tracial state is the zero functional. -/
theorem tracialState_toLinearMap_ne_zero {A : Type*} [CStarAlgebra A] (τ : TracialState A) :
    τ.toLinearMap ≠ 0 := by
  intro h
  have h1 := τ.map_one
  rw [h, LinearMap.zero_apply] at h1
  exact zero_ne_one h1

/-! ### Normalizations -/

theorem normalizedTrace_one (Y : FiniteCarrier) [Nonempty Y] : normalizedTrace Y 1 = 1 := by
  have hne : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold normalizedTrace
  rw [Matrix.trace_one, div_self hne]

theorem hilbertSchmidtNorm_zero (Y : FiniteCarrier) : hilbertSchmidtNorm Y 0 = 0 := by
  simp [hilbertSchmidtNorm]

theorem hilbertSchmidtNorm_one (Y : FiniteCarrier) [Nonempty Y] :
    hilbertSchmidtNorm Y 1 = 1 := by
  have hne : ((Fintype.card Y : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hrow : ∀ i : Y, (∑ j : Y, Complex.normSq ((1 : Matrix Y Y ℂ) i j)) = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Matrix.one_apply_ne hji.symm]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hsum : (∑ i : Y, ∑ j : Y, Complex.normSq ((1 : Matrix Y Y ℂ) i j))
      = (Fintype.card Y : ℝ) := by
    simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  unfold hilbertSchmidtNorm
  rw [hsum, div_self hne, Real.sqrt_one]

/-! ### Complete positivity -/

/-- The scalar embedding `z ↦ z · 1` of `ℂ` into `M_Y(ℂ)`. -/
def scalarMap (Y : FiniteCarrier) : ℂ →ₗ[ℂ] Matrix Y Y ℂ where
  toFun z := Matrix.diagonal fun _ ↦ z
  map_add' z w := by
    ext p q
    by_cases hpq : p = q <;> simp [hpq]
  map_smul' c z := by
    ext p q
    by_cases hpq : p = q <;> simp [hpq]

@[simp] theorem scalarMap_apply (Y : FiniteCarrier) (z : ℂ) :
    scalarMap Y z = Matrix.diagonal fun _ ↦ z := rfl

theorem scalarMap_mul (Y : FiniteCarrier) (z w : ℂ) :
    scalarMap Y (z * w) = scalarMap Y z * scalarMap Y w := by
  simp only [scalarMap_apply, Matrix.diagonal_mul_diagonal]

theorem scalarMap_one (Y : FiniteCarrier) : scalarMap Y 1 = 1 := by
  simp only [scalarMap_apply, Matrix.diagonal_one]

theorem normalizedTrace_scalarMap (Y : FiniteCarrier) [Nonempty Y] (z : ℂ) :
    normalizedTrace Y (scalarMap Y z) = z := by
  have hne : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  show Matrix.trace (scalarMap Y z) / ((Fintype.card Y : ℕ) : ℂ) = z
  rw [scalarMap_apply, Matrix.trace_diagonal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_comm, mul_div_assoc, div_self hne, mul_one]

/-- Permuting a triple sum so that the innermost index becomes the outermost. -/
theorem sum_comm₃ {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (f : ι → κ → ν → ℂ) :
    (∑ i : ι, ∑ j : κ, ∑ z : ν, f i j z) = ∑ z : ν, ∑ i : ι, ∑ j : κ, f i j z := by
  have h1 : ∀ i : ι, (∑ j : κ, ∑ z : ν, f i j z) = ∑ z : ν, ∑ j : κ, f i j z :=
    fun _ ↦ Finset.sum_comm
  simp_rw [h1]
  exact Finset.sum_comm

/-- The scalar embedding is completely positive: its form is `∑ₚ |∑ᵢ zᵢ ξᵢ(p)|²`. -/
theorem isCompletelyPositive_scalarMap (Y : FiniteCarrier) :
    IsCompletelyPositive Y (scalarMap Y) := by
  intro m z w
  have hcollapse : ∀ (i j : Fin m) (p : Y),
      (∑ q : Y, star (w i p) * scalarMap Y (star (z i) * z j) p q * w j q)
        = star (z i * w i p) * (z j * w j p) := by
    intro i j p
    have hterm : ∀ q : Y, star (w i p) * scalarMap Y (star (z i) * z j) p q * w j q
        = if p = q then star (w i p) * (star (z i) * z j) * w j q else 0 := by
      intro q
      by_cases hpq : p = q <;> simp [hpq]
    rw [Finset.sum_congr rfl fun q _ ↦ hterm q,
      Finset.sum_ite_eq Finset.univ p
        (fun q ↦ star (w i p) * (star (z i) * z j) * w j q)]
    simp only [Finset.mem_univ, if_true, star_mul]
    ring
  have hsum : (∑ i : Fin m, ∑ j : Fin m, ∑ p : Y, ∑ q : Y,
      star (w i p) * scalarMap Y (star (z i) * z j) p q * w j q)
      = ∑ p : Y, star (∑ i : Fin m, z i * w i p) * (∑ j : Fin m, z j * w j p) := by
    have h1 : ∀ i j : Fin m, (∑ p : Y, ∑ q : Y,
        star (w i p) * scalarMap Y (star (z i) * z j) p q * w j q)
        = ∑ p : Y, star (z i * w i p) * (z j * w j p) :=
      fun i j ↦ Finset.sum_congr rfl fun p _ ↦ hcollapse i j p
    simp_rw [h1]
    rw [sum_comm₃ (fun (i j : Fin m) (p : Y) ↦ star (z i * w i p) * (z j * w j p))]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [star_sum]
    exact (Finset.sum_mul_sum Finset.univ Finset.univ
      (fun i ↦ star (z i * w i p)) (fun j ↦ z j * w j p)).symm
  have hreal : (∑ p : Y, star (∑ i : Fin m, z i * w i p) * (∑ j : Fin m, z j * w j p))
      = (((∑ p : Y, Complex.normSq (∑ i : Fin m, z i * w i p)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [hsum, hreal]
  exact Complex.zero_le_real.2 (Finset.sum_nonneg fun p _ ↦ Complex.normSq_nonneg _)

/-- A one-point carrier. -/
abbrev oneCarrier : FiniteCarrier :=
  ⟨Unit, inferInstance, inferInstance⟩

instance : Nonempty oneCarrier :=
  ⟨()⟩

/-- The negated scalar embedding is not completely positive: its form at `a = 1`, `ξ = 1` is
`-1`. -/
theorem not_isCompletelyPositive_neg_scalarMap :
    ¬ IsCompletelyPositive oneCarrier (-scalarMap oneCarrier) := by
  intro h
  have he : scalarMap oneCarrier 1 () () = 1 := by
    rw [scalarMap_one, Matrix.one_apply_eq]
  have h1 := h 1 (fun _ ↦ 1) (fun _ _ ↦ 1)
  have h2 : (0 : ℂ) ≤ -1 := by simpa [he] using h1
  exact absurd (Complex.nonneg_iff.1 h2).1 (by norm_num)

/-! ### Amenable and quasidiagonal traces -/

/-- The trace clause for the constant scalar model of a tracial state on `ℂ`. -/
theorem tendsto_trace_scalarMap (τ : TracialState ℂ) (a : ℂ) :
    Tendsto (fun _ : ℕ ↦ ‖τ.toLinearMap a - normalizedTrace oneCarrier (scalarMap oneCarrier a)‖)
      atTop (nhds 0) := by
  have h0 : ‖τ.toLinearMap a - normalizedTrace oneCarrier (scalarMap oneCarrier a)‖ = 0 := by
    rw [tracialState_complex_apply, normalizedTrace_scalarMap, sub_self, norm_zero]
  rw [h0]
  exact tendsto_const_nhds

/-- Every tracial state on `ℂ` is quasidiagonal: the scalar embedding into `M_1(ℂ)` is an exact
model. -/
def complexQuasidiagonalTraceModel (τ : TracialState ℂ) : QuasidiagonalTraceModel τ where
  space _ := oneCarrier
  map _ := scalarMap oneCarrier
  map_one _ := scalarMap_one oneCarrier
  completelyPositive _ := isCompletelyPositive_scalarMap oneCarrier
  tendsto_mul a b := by
    have h0 : ‖scalarMap oneCarrier (a * b)
        - scalarMap oneCarrier a * scalarMap oneCarrier b‖ = 0 := by
      rw [scalarMap_mul, sub_self, norm_zero]
    exact tendsto_const_nhds.congr fun _ ↦ h0.symm
  tendsto_trace a := tendsto_trace_scalarMap τ a

/-- Every tracial state on `ℂ` is amenable, with the same model. -/
def complexAmenableTraceModel (τ : TracialState ℂ) : AmenableTraceModel τ where
  space _ := oneCarrier
  map _ := scalarMap oneCarrier
  map_one _ := scalarMap_one oneCarrier
  completelyPositive _ := isCompletelyPositive_scalarMap oneCarrier
  tendsto_mul a b := by
    have h0 : hilbertSchmidtNorm oneCarrier (scalarMap oneCarrier (a * b)
        - scalarMap oneCarrier a * scalarMap oneCarrier b) = 0 := by
      rw [scalarMap_mul, sub_self, hilbertSchmidtNorm_zero]
    exact tendsto_const_nhds.congr fun _ ↦ h0.symm
  tendsto_trace a := tendsto_trace_scalarMap τ a

theorem isQuasidiagonalTrace_complex (τ : TracialState ℂ) : IsQuasidiagonalTrace τ :=
  ⟨complexQuasidiagonalTraceModel τ⟩

theorem isAmenableTrace_complex (τ : TracialState ℂ) : IsAmenableTrace τ :=
  ⟨complexAmenableTraceModel τ⟩

/-- On `ℂ` every amenable tracial state is quasidiagonal, so the printed universal holds for this
algebra and a counterexample must be larger. -/
theorem amenable_imp_quasidiagonal_complex (τ : TracialState ℂ) (_h : IsAmenableTrace τ) :
    IsQuasidiagonalTrace τ :=
  isQuasidiagonalTrace_complex τ

/-- The trace clause pins the state: if the maps of a quasidiagonal model of `τ` also have
normalized traces converging to `τ'`, then `τ' = τ`. -/
theorem state_eq_of_quasidiagonalTraceModel {A : Type*} [CStarAlgebra A] {τ : TracialState A}
    (M : QuasidiagonalTraceModel τ) (τ' : TracialState A)
    (h : ∀ a : A, Tendsto (fun n ↦ ‖τ'.toLinearMap a
      - normalizedTrace (M.space n) (M.map n a)‖) atTop (nhds 0)) :
    τ'.toLinearMap = τ.toLinearMap := by
  ext a
  have h1 : Tendsto (fun n ↦ normalizedTrace (M.space n) (M.map n a)) atTop
      (nhds (τ'.toLinearMap a)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact (h a).congr fun _ ↦ norm_sub_rev _ _
  have h2 : Tendsto (fun n ↦ normalizedTrace (M.space n) (M.map n a)) atTop
      (nhds (τ.toLinearMap a)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact (M.tendsto_trace a).congr fun _ ↦ norm_sub_rev _ _
  exact tendsto_nhds_unique h1 h2

/-- In every quasidiagonal model the matrix sizes are eventually positive, because `τ(1) = 1`. -/
theorem eventually_nonempty_space {A : Type*} [CStarAlgebra A] {τ : TracialState A}
    (M : QuasidiagonalTraceModel τ) : ∀ᶠ n in atTop, Nonempty (M.space n) := by
  filter_upwards [(M.tendsto_trace 1).eventually (gt_mem_nhds one_pos)] with n hn
  by_contra hne
  have hcard : Fintype.card (M.space n) = 0 :=
    Fintype.card_eq_zero_iff.2 (not_nonempty_iff.1 hne)
  have htr : normalizedTrace (M.space n) (M.map n 1) = 0 := by
    unfold normalizedTrace
    rw [hcard, Nat.cast_zero, div_zero]
  have hlt : ‖τ.toLinearMap 1 - normalizedTrace (M.space n) (M.map n 1)‖ < 1 := hn
  rw [htr, sub_zero, τ.map_one, norm_one] at hlt
  exact lt_irrefl _ hlt

end

end ModelTests
end STWProblemX1
