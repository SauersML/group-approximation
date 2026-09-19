import GroupApproximation.Sofic.NormTraceGap
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Operator-norm tensor amplification

This file isolates the finite-dimensional analytic construction needed in a
marked-limit argument for MF groups.  A single tensor power is not a valid
uniform separator: scalar phases can wrap back to `1`.  The correct amplifier
is a block sum of the first several tensor powers.  The first layer below is
the dimension-free operator-norm estimate which makes that construction
compatible with increasingly accurate almost representations.

We use a recursively nested product as the tensor-power index.  This avoids
all reindexing overhead in the inductive estimates; it is canonically
equivalent to the usual `Fin n → Y` index used by `tensorPow` elsewhere in the
library.
-/

namespace GroupApproximation

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

noncomputable section

/-! ## The operator norm of a Kronecker product -/

variable {Y Z : Type} [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- The Euclidean operator norm of a Kronecker product is at most the product
of the two operator norms.  The proof applies the two matrices successively
to the two coordinates and uses the matrix-vector bound in each coordinate.
-/
theorem l2_opNorm_kronecker_le (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq
    ⟨Y × Z, inferInstance, inferInstance⟩ (A ⊗ₖ B)
      (M := ‖A‖ * ‖B‖) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  intro x
  let y : Y → Z → ℂ := fun j k ↦ ∑ l : Z, B k l * x (j, l)
  have happly (i : Y) (k : Z) :
      ((A ⊗ₖ B) *ᵥ x) (i, k) = ∑ j : Y, A i j * y j k := by
    change (∑ jk : Y × Z, (A i jk.1 * B k jk.2) * x jk) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    simp only [y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  let Y₀ : FiniteModel := ⟨Y, inferInstance, inferInstance⟩
  let Z₀ : FiniteModel := ⟨Z, inferInstance, inferInstance⟩
  have hA (k : Z) :
      ∑ i : Y, Complex.normSq (∑ j : Y, A i j * y j k) ≤
        ‖A‖ ^ 2 * ∑ j : Y, Complex.normSq (y j k) := by
    simpa only [Matrix.mulVec, dotProduct] using
      sum_normSq_mulVec_le Y₀ A (fun j ↦ y j k)
  have hB (j : Y) :
      ∑ k : Z, Complex.normSq (y j k) ≤
        ‖B‖ ^ 2 * ∑ l : Z, Complex.normSq (x (j, l)) := by
    simpa only [Matrix.mulVec, dotProduct, y] using
      sum_normSq_mulVec_le Z₀ B (fun l ↦ x (j, l))
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [happly]
  calc
    ∑ i : Y, ∑ k : Z, Complex.normSq (∑ j : Y, A i j * y j k) =
        ∑ k : Z, ∑ i : Y, Complex.normSq (∑ j : Y, A i j * y j k) :=
      Finset.sum_comm
    _ ≤ ∑ k : Z, ‖A‖ ^ 2 * ∑ j : Y, Complex.normSq (y j k) :=
      Finset.sum_le_sum fun k _ ↦ hA k
    _ = ‖A‖ ^ 2 * ∑ j : Y, ∑ k : Z, Complex.normSq (y j k) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ‖A‖ ^ 2 *
        ∑ j : Y, ‖B‖ ^ 2 * ∑ l : Z, Complex.normSq (x (j, l)) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ ↦ hB j) (sq_nonneg _)
    _ = (‖A‖ * ‖B‖) ^ 2 *
        ∑ j : Y, ∑ l : Z, Complex.normSq (x (j, l)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-! ## A disk point cannot hide from all of its first powers -/

/-- If `a` lies in the closed unit disk and is separated from `1` in real
part, one of its first `N` powers has real part below `1/2`, provided `N` is
large compared with that real-part gap.  Keeping all first powers in a single
block sum is essential: an individual power can wrap a scalar phase back to
`1`.

The proof is the geometric-series estimate
`gap * ‖∑ a^(k+1)‖ ≤ 2`. -/
theorem exists_pow_re_lt_half (a : ℂ) {gap : ℝ}
    (hgap : 0 < gap) (ha : ‖a‖ ≤ 1) (hre : gap ≤ 1 - a.re)
    (N : ℕ) (hN : 4 < (N : ℝ) * gap) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ N ∧ (a ^ p).re < (1 / 2 : ℝ) := by
  classical
  by_contra hnone
  push Not at hnone
  let S : ℂ := ∑ k ∈ Finset.range N, a ^ (k + 1)
  have hterm (k : ℕ) (hk : k ∈ Finset.range N) :
      (1 / 2 : ℝ) ≤ (a ^ (k + 1)).re := by
    have hkN : k + 1 ≤ N := by
      simp only [Finset.mem_range] at hk
      omega
    exact hnone (k + 1) (by omega) hkN
  have hSre : (N : ℝ) / 2 ≤ S.re := by
    dsimp [S]
    rw [Complex.re_sum]
    calc
      (N : ℝ) / 2 = ∑ _k ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ ∑ k ∈ Finset.range N, (a ^ (k + 1)).re :=
        Finset.sum_le_sum fun k hk ↦ hterm k hk
  have hgapNorm : gap ≤ ‖1 - a‖ := by
    calc
      gap ≤ 1 - a.re := hre
      _ = (1 - a).re := by simp
      _ ≤ |(1 - a).re| := le_abs_self _
      _ ≤ ‖1 - a‖ := Complex.abs_re_le_norm _
  have hgeom : (1 - a) * S = a - a ^ (N + 1) := by
    have hseries : S = a * ∑ k ∈ Finset.range N, a ^ k := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← pow_succ']
    rw [hseries]
    calc
      (1 - a) * (a * ∑ k ∈ Finset.range N, a ^ k) =
          a * ((∑ k ∈ Finset.range N, a ^ k) * (1 - a)) := by ring
      _ = a * (1 - a ^ N) := by rw [geom_sum_mul_neg]
      _ = a - a ^ (N + 1) := by rw [pow_succ]; ring
  have hSnorm : gap * ‖S‖ ≤ 2 := by
    calc
      gap * ‖S‖ ≤ ‖1 - a‖ * ‖S‖ :=
        mul_le_mul_of_nonneg_right hgapNorm (norm_nonneg _)
      _ = ‖(1 - a) * S‖ := (norm_mul _ _).symm
      _ = ‖a - a ^ (N + 1)‖ := by rw [hgeom]
      _ ≤ ‖a‖ + ‖a ^ (N + 1)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
        gcongr
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg a) ha
      _ = 2 := by norm_num
  have hSlarge : (N : ℝ) / 2 ≤ ‖S‖ :=
    hSre.trans ((le_abs_self S.re).trans (Complex.abs_re_le_norm S))
  nlinarith [mul_le_mul_of_nonneg_left hSlarge hgap.le, hSnorm]

/-! ## Recursive tensor powers -/

/-- Nested product index for a tensor power. -/
@[reducible] def OpTensorIndex (Y : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => Y × OpTensorIndex Y n

@[reducible] private def opTensorIndexFintype :
    (n : ℕ) → Fintype (OpTensorIndex Y n)
  | 0 => inferInstance
  | n + 1 => by
      letI : Fintype (OpTensorIndex Y n) := opTensorIndexFintype n
      exact inferInstanceAs (Fintype (Y × OpTensorIndex Y n))

@[reducible] private def opTensorIndexDecidableEq :
    (n : ℕ) → DecidableEq (OpTensorIndex Y n)
  | 0 => inferInstance
  | n + 1 => by
      letI : DecidableEq (OpTensorIndex Y n) := opTensorIndexDecidableEq n
      exact inferInstanceAs (DecidableEq (Y × OpTensorIndex Y n))

omit [Fintype Y] [DecidableEq Y] in
private theorem opTensorIndexNonempty (hY : Nonempty Y) :
    (n : ℕ) → Nonempty (OpTensorIndex Y n)
  | 0 => inferInstance
  | n + 1 => ⟨hY.some, (opTensorIndexNonempty hY n).some⟩

@[reducible, instance] def instOpTensorIndexFintype (n : ℕ) :
    Fintype (OpTensorIndex Y n) := opTensorIndexFintype n

@[reducible, instance] def instOpTensorIndexDecidableEq (n : ℕ) :
    DecidableEq (OpTensorIndex Y n) := opTensorIndexDecidableEq n

/-- The finite model underlying the recursively indexed tensor power. -/
@[reducible] def opTensorModel (Y : FiniteModel) (n : ℕ) : FiniteModel :=
  ⟨OpTensorIndex Y n, inferInstance, inferInstance⟩

/-- Recursive Kronecker power, with the zeroth power on the one-point space. -/
def opTensorPow (A : Matrix Y Y ℂ) :
    (n : ℕ) → Matrix (OpTensorIndex Y n) (OpTensorIndex Y n) ℂ
  | 0 => 1
  | n + 1 => A ⊗ₖ opTensorPow A n

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem opTensorPow_zero (A : Matrix Y Y ℂ) :
    opTensorPow A 0 = 1 := rfl

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem opTensorPow_succ (A : Matrix Y Y ℂ) (n : ℕ) :
    opTensorPow A (n + 1) = A ⊗ₖ opTensorPow A n := rfl

/-- The constant multi-index used to read a diagonal coefficient from every
tensor factor. -/
def opTensorRepeat (i : Y) : (n : ℕ) → OpTensorIndex Y n
  | 0 => PUnit.unit
  | n + 1 => (i, opTensorRepeat i n)

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem opTensorPow_repeat_apply (A : Matrix Y Y ℂ) (i : Y) (n : ℕ) :
    opTensorPow A n (opTensorRepeat i n) (opTensorRepeat i n) = (A i i) ^ n := by
  induction n with
  | zero => simp [opTensorPow]
  | succ n ih =>
      change A i i * opTensorPow A n (opTensorRepeat i n) (opTensorRepeat i n) = _
      rw [ih, pow_succ, mul_comm]

omit [Fintype Y] in
theorem opTensorPow_one (n : ℕ) :
    opTensorPow (1 : Matrix Y Y ℂ) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [opTensorPow_succ, ih, one_kronecker_one]

omit [DecidableEq Y] in
theorem opTensorPow_mul (A B : Matrix Y Y ℂ) (n : ℕ) :
    opTensorPow (A * B) n = opTensorPow A n * opTensorPow B n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [opTensorPow_succ, opTensorPow_succ, opTensorPow_succ, ih,
        mul_kronecker_mul]

omit [Fintype Y] [DecidableEq Y] in
theorem opTensorPow_conjTranspose (A : Matrix Y Y ℂ) (n : ℕ) :
    (opTensorPow A n)ᴴ = opTensorPow Aᴴ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [opTensorPow_succ, opTensorPow_succ, conjTranspose_kronecker, ih]

theorem opTensorPow_mem_unitaryGroup {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (n : ℕ) :
    opTensorPow A n ∈ Matrix.unitaryGroup (OpTensorIndex Y n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    opTensorPow_conjTranspose, ← opTensorPow_mul]
  have hAA : A * Aᴴ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hA
    exact hA
  rw [hAA, opTensorPow_one]

/-- Tensoring a matrix `n` times costs at most the `n`-th power of its norm. -/
theorem l2_opNorm_opTensorPow_le (A : Matrix Y Y ℂ) (n : ℕ) :
    ‖opTensorPow A n‖ ≤ ‖A‖ ^ n := by
  induction n with
  | zero => rw [opTensorPow_zero, norm_one]; exact le_rfl
  | succ n ih =>
      rw [opTensorPow_succ, pow_succ]
      simpa only [mul_comm] using
        (l2_opNorm_kronecker_le A (opTensorPow A n)).trans
          (mul_le_mul_of_nonneg_left ih (norm_nonneg A))

/-- **Tensor-power telescoping.**  On unitary inputs the operator-norm error
of the `n`-fold tensor powers is at most `n` times the original error. -/
theorem l2_opNorm_opTensorPow_sub_le {A B : Matrix Y Y ℂ}
    (hY : Nonempty Y)
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) (n : ℕ) :
    ‖opTensorPow A n - opTensorPow B n‖ ≤ n * ‖A - B‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      letI : Nonempty Y := hY
      letI : Nonempty (OpTensorIndex Y n) := opTensorIndexNonempty hY n
      rw [opTensorPow_succ, opTensorPow_succ]
      have hsplit :
          A ⊗ₖ opTensorPow A n - B ⊗ₖ opTensorPow B n =
            (A - B) ⊗ₖ opTensorPow A n +
              B ⊗ₖ (opTensorPow A n - opTensorPow B n) := by
        ext ⟨i, k⟩ ⟨j, l⟩
        simp only [Matrix.sub_apply, Matrix.add_apply, kronecker_apply]
        ring
      rw [hsplit]
      calc
        ‖(A - B) ⊗ₖ opTensorPow A n +
            B ⊗ₖ (opTensorPow A n - opTensorPow B n)‖ ≤
            ‖(A - B) ⊗ₖ opTensorPow A n‖ +
              ‖B ⊗ₖ (opTensorPow A n - opTensorPow B n)‖ := norm_add_le _ _
        _ ≤ ‖A - B‖ * ‖opTensorPow A n‖ +
              ‖B‖ * ‖opTensorPow A n - opTensorPow B n‖ :=
          add_le_add (l2_opNorm_kronecker_le _ _) (l2_opNorm_kronecker_le _ _)
        _ ≤ ‖A - B‖ * 1 + 1 * (n * ‖A - B‖) := by
          have hpowA := CStarRing.norm_of_mem_unitary
            (opTensorPow_mem_unitaryGroup hA n)
          have hnormB := CStarRing.norm_of_mem_unitary hB
          rw [hpowA, hnormB]
          simpa using add_le_add_left ih ‖A - B‖
        _ = ((n : ℝ) + 1) * ‖A - B‖ := by ring
        _ = (↑(n + 1) : ℝ) * ‖A - B‖ := by
          norm_num

/-! ## Bounded-power separation -/

/-- The squared mass of one row is bounded by the squared operator norm. -/
theorem sum_row_normSq_le_sq_l2_opNorm (C : Matrix Y Y ℂ) (i : Y) :
    ∑ j : Y, Complex.normSq (C i j) ≤ ‖C‖ ^ 2 := by
  classical
  let Y₀ : FiniteModel := ⟨Y, inferInstance, inferInstance⟩
  have h := sum_normSq_mulVec_le Y₀ Cᴴ (Pi.single i 1)
  have hcol (j : Y) :
      (Cᴴ *ᵥ Pi.single i (1 : ℂ)) j = (starRingEnd ℂ) (C i j) := by
    rw [Matrix.mulVec_single_one]
    change Cᴴ j i = _
    rw [Matrix.conjTranspose_apply]
    rfl
  have hsingle :
      ∑ j : Y, Complex.normSq ((Pi.single i (1 : ℂ) : Y → ℂ) j) = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  calc
    ∑ j : Y, Complex.normSq (C i j) =
        ∑ j : Y, Complex.normSq ((Cᴴ *ᵥ Pi.single i (1 : ℂ)) j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcol, Complex.normSq_conj]
    _ ≤ ‖Cᴴ‖ ^ 2 *
        ∑ j : Y, Complex.normSq ((Pi.single i (1 : ℂ) : Y → ℂ) j) := h
    _ = ‖C‖ ^ 2 := by
      rw [hsingle, mul_one, ← Matrix.star_eq_conjTranspose, norm_star]

/-- A repeated tensor row records the corresponding diagonal coefficient to
the same power. -/
theorem sum_row_normSq_opTensorPow_sub_one
    {A : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (i : Y) (n : ℕ) :
    ∑ j : OpTensorIndex Y n,
        Complex.normSq ((opTensorPow A n - 1) (opTensorRepeat i n) j) =
      2 - 2 * ((A i i) ^ n).re := by
  classical
  let Yn : FiniteModel := opTensorModel ⟨Y, inferInstance, inferInstance⟩ n
  let r : OpTensorIndex Y n := opTensorRepeat i n
  have hU := opTensorPow_mem_unitaryGroup hA n
  have hone : (1 : Matrix (OpTensorIndex Y n) (OpTensorIndex Y n) ℂ) ∈
      Matrix.unitaryGroup (OpTensorIndex Y n) ℂ := one_mem _
  have hcross :
      ∑ j : OpTensorIndex Y n,
          ((opTensorPow A n) r j *
            (starRingEnd ℂ) ((1 : Matrix (OpTensorIndex Y n)
              (OpTensorIndex Y n) ℂ) r j)).re = ((A i i) ^ n).re := by
    rw [Finset.sum_eq_single r]
    · simp [r, opTensorPow_repeat_apply]
    · intro j _ hj
      rw [Matrix.one_apply_ne hj.symm, map_zero, mul_zero, Complex.zero_re]
    · simp
  simp only [Matrix.sub_apply, normSq_sub_expand]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hcross, row_normSq_of_unitary Yn hU r, row_normSq_of_unitary Yn hone r]
  ring

/-- If one diagonal coefficient has a fixed real-part gap, one of the first
`N` tensor powers is more than distance `1` from the identity.  This is the
strong separation normalization used by the marked-limit construction. -/
theorem exists_opTensorPow_norm_sub_one_gt_one_of_diagonal_gap
    {A : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (i : Y) {gap : ℝ} (hgap : 0 < gap) (hre : gap ≤ 1 - (A i i).re)
    (N : ℕ) (hN : 4 < (N : ℝ) * gap) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ N ∧ ‖opTensorPow A p - 1‖ > 1 := by
  have ha : ‖A i i‖ ≤ 1 := entry_norm_bound_of_unitary hA i i
  obtain ⟨p, hp1, hpN, hp⟩ := exists_pow_re_lt_half (A i i) hgap ha hre N hN
  refine ⟨p, hp1, hpN, ?_⟩
  have hrow := sum_row_normSq_opTensorPow_sub_one hA i p
  have hbound := sum_row_normSq_le_sq_l2_opNorm
    (opTensorPow A p - 1) (opTensorRepeat i p)
  rw [hrow] at hbound
  nlinarith [norm_nonneg (opTensorPow A p - 1)]

end

end GroupApproximation
