import GroupApproximation.Monsters.ExplicitLinearModel
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Upper-triangular matrices and the dyadic grid

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform`: property A of `Σ ≤ GL₄(ℚ)` is obtained, following
Guentner--Higson--Weinberger, from a coarse embedding of `Σ` into the solvable
group of upper-triangular matrices.  This file provides the linear algebra:

* the Borel subgroup `borel ≤ GL₄(ℚ)` of units that are upper triangular
  together with their inverses;
* dyadic diagonal matrices `twoDiag k = diag(2^{k₀}, …, 2^{k₃})`;
* **grid points** `b = twoDiag k · m` with `m` integral unitriangular with
  integral unitriangular inverse;
* `isIntegral_pow_smul_gridQuotient`: a quotient `b⁻¹ b'` of grid points has
  entries in `2^{-E} ℤ` as soon as the diagonal of `b'⁻¹ b` is bounded by `2^E`.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExplicitLinearModel

/-- Upper triangularity of a `4 × 4` rational matrix. -/
def IsUpperTri (m : Mat) : Prop :=
  ∀ i j : Fin 4, j < i → m i j = 0

theorem isUpperTri_one : IsUpperTri (1 : Mat) :=
  fun _ _ hji ↦ Matrix.one_apply_ne hji.ne'

theorem isUpperTri_diagonal (d : Fin 4 → ℚ) : IsUpperTri (Matrix.diagonal d) :=
  fun _ _ hji ↦ Matrix.diagonal_apply_ne d hji.ne'

theorem isUpperTri_mul {a b : Mat} (ha : IsUpperTri a) (hb : IsUpperTri b) :
    IsUpperTri (a * b) := by
  intro i j hji
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hki : k < i
  · rw [ha i k hki, zero_mul]
  · rw [hb k j (lt_of_lt_of_le hji (not_lt.mp hki)), mul_zero]

/-- The diagonal of a product of upper-triangular matrices is the product of
the diagonals. -/
theorem upperTri_mul_apply_diag {a b : Mat} (ha : IsUpperTri a) (hb : IsUpperTri b)
    (i : Fin 4) : (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hki ↦ ?_) (fun h ↦ absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hki with h | h
  · rw [ha i k h, zero_mul]
  · rw [hb k i h, mul_zero]

/-- **The Borel subgroup** of `GL₄(ℚ)`: units upper triangular together with
their inverses. -/
def borel : Subgroup Matˣ where
  carrier := {u | IsUpperTri (u : Mat) ∧ IsUpperTri ((u⁻¹ : Matˣ) : Mat)}
  mul_mem' := by
    intro u v hu hv
    obtain ⟨hu1, hu2⟩ : IsUpperTri (u : Mat) ∧ IsUpperTri ((u⁻¹ : Matˣ) : Mat) := hu
    obtain ⟨hv1, hv2⟩ : IsUpperTri (v : Mat) ∧ IsUpperTri ((v⁻¹ : Matˣ) : Mat) := hv
    show IsUpperTri ((u * v : Matˣ) : Mat) ∧ IsUpperTri (((u * v)⁻¹ : Matˣ) : Mat)
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact isUpperTri_mul hu1 hv1
    · rw [mul_inv_rev, Units.val_mul]
      exact isUpperTri_mul hv2 hu2
  one_mem' := by
    show IsUpperTri ((1 : Matˣ) : Mat) ∧ IsUpperTri (((1 : Matˣ)⁻¹ : Matˣ) : Mat)
    refine ⟨?_, ?_⟩
    · rw [Units.val_one]
      exact isUpperTri_one
    · rw [inv_one, Units.val_one]
      exact isUpperTri_one
  inv_mem' := by
    intro u hu
    obtain ⟨hu1, hu2⟩ : IsUpperTri (u : Mat) ∧ IsUpperTri ((u⁻¹ : Matˣ) : Mat) := hu
    show IsUpperTri ((u⁻¹ : Matˣ) : Mat) ∧ IsUpperTri ((u⁻¹⁻¹ : Matˣ) : Mat)
    refine ⟨hu2, ?_⟩
    rw [inv_inv]
    exact hu1

theorem mem_borel {u : Matˣ} :
    u ∈ borel ↔ IsUpperTri (u : Mat) ∧ IsUpperTri ((u⁻¹ : Matˣ) : Mat) :=
  Iff.rfl

/-- Dyadic diagonal matrices `diag(2^{k₀}, 2^{k₁}, 2^{k₂}, 2^{k₃})`. -/
def twoDiag (k : Fin 4 → ℤ) : Mat :=
  Matrix.diagonal fun i ↦ (2 : ℚ) ^ k i

theorem isUpperTri_twoDiag (k : Fin 4 → ℤ) : IsUpperTri (twoDiag k) :=
  isUpperTri_diagonal _

theorem twoDiag_mul (a b : Fin 4 → ℤ) : twoDiag a * twoDiag b = twoDiag (a + b) := by
  show Matrix.diagonal (fun i ↦ (2 : ℚ) ^ a i) * Matrix.diagonal (fun i ↦ (2 : ℚ) ^ b i) =
    Matrix.diagonal (fun i ↦ (2 : ℚ) ^ (a + b) i)
  rw [Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal
    (funext fun i ↦ (zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0) (a i) (b i)).symm)

theorem twoDiag_zero : twoDiag 0 = 1 := by
  have h : (fun i : Fin 4 ↦ (2 : ℚ) ^ (0 : Fin 4 → ℤ) i) = fun _ ↦ 1 :=
    funext fun _ ↦ zpow_zero (2 : ℚ)
  show Matrix.diagonal (fun i : Fin 4 ↦ (2 : ℚ) ^ (0 : Fin 4 → ℤ) i) = 1
  rw [h, Matrix.diagonal_one]

theorem twoDiag_mul_twoDiag_neg (k : Fin 4 → ℤ) : twoDiag k * twoDiag (-k) = 1 := by
  rw [twoDiag_mul, add_neg_cancel, twoDiag_zero]

/-- Integral unitriangular units with integral unitriangular inverses
(the group `N(ℤ)`). -/
def IsIntegralUnitriangular (m : Matˣ) : Prop :=
  IsIntegralUnit m ∧ IsUpperTri (m : Mat) ∧ IsUpperTri ((m⁻¹ : Matˣ) : Mat) ∧
    ∀ i, (m : Mat) i i = 1 ∧ ((m⁻¹ : Matˣ) : Mat) i i = 1

/-- **Grid points** of the Borel group: `b = twoDiag k · m` with `m ∈ N(ℤ)`. -/
def IsGridPoint (b : Matˣ) : Prop :=
  ∃ k : Fin 4 → ℤ, ∃ m : Matˣ, IsIntegralUnitriangular m ∧ (b : Mat) = twoDiag k * (m : Mat)

theorem val_inv_of_eq_twoDiag_mul {b m : Matˣ} {k : Fin 4 → ℤ}
    (h : (b : Mat) = twoDiag k * (m : Mat)) :
    ((b⁻¹ : Matˣ) : Mat) = ((m⁻¹ : Matˣ) : Mat) * twoDiag (-k) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [h, mul_assoc, ← mul_assoc (m : Mat), Units.mul_inv, one_mul, twoDiag_mul_twoDiag_neg]

theorem IsGridPoint.mem_borel {b : Matˣ} (hb : IsGridPoint b) : b ∈ borel := by
  obtain ⟨k, m, ⟨-, hm1, hm2, -⟩, h⟩ := hb
  refine NN09b.mem_borel.mpr ⟨?_, ?_⟩
  · rw [h]
    exact isUpperTri_mul (isUpperTri_twoDiag k) hm1
  · rw [val_inv_of_eq_twoDiag_mul h]
    exact isUpperTri_mul hm2 (isUpperTri_twoDiag (-k))

/-- `2^E · twoDiag d` is integral once every exponent `E + d l` is
nonnegative. -/
theorem isIntegral_pow_smul_twoDiag (E : ℕ) (d : Fin 4 → ℤ) (hd : ∀ l, 0 ≤ (E : ℤ) + d l) :
    IsIntegral ((2 : ℚ) ^ E • twoDiag d) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (hd i)
    have hval : ((2 : ℚ) ^ E • twoDiag d) i i = (2 : ℚ) ^ n := by
      rw [Matrix.smul_apply, twoDiag, Matrix.diagonal_apply_eq]
      show (2 : ℚ) ^ E * (2 : ℚ) ^ d i = (2 : ℚ) ^ n
      rw [← zpow_natCast, ← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hn]
      exact zpow_natCast (2 : ℚ) n
    rw [hval]
    exact ⟨2 ^ n, by norm_num⟩
  · have hval : ((2 : ℚ) ^ E • twoDiag d) i j = 0 := by
      rw [Matrix.smul_apply, twoDiag, Matrix.diagonal_apply_ne _ hij]
      exact mul_zero _
    rw [hval]
    exact ⟨0, by norm_num⟩

/-- The quotient of two grid points, in coordinates. -/
theorem val_gridQuotient {b b' m m' : Matˣ} {k k' : Fin 4 → ℤ}
    (h : (b : Mat) = twoDiag k * (m : Mat)) (h' : (b' : Mat) = twoDiag k' * (m' : Mat)) :
    ((b⁻¹ * b' : Matˣ) : Mat) = ((m⁻¹ : Matˣ) : Mat) * twoDiag (-k + k') * (m' : Mat) := by
  rw [Units.val_mul, val_inv_of_eq_twoDiag_mul h, h', mul_assoc,
    ← mul_assoc (twoDiag (-k)), twoDiag_mul, ← mul_assoc]

/-- The diagonal of the quotient of two grid points is dyadic. -/
theorem gridQuotient_apply_diag {b b' m m' : Matˣ} {k k' : Fin 4 → ℤ}
    (hm : IsIntegralUnitriangular m) (hm' : IsIntegralUnitriangular m')
    (h : (b : Mat) = twoDiag k * (m : Mat)) (h' : (b' : Mat) = twoDiag k' * (m' : Mat))
    (l : Fin 4) :
    ((b⁻¹ * b' : Matˣ) : Mat) l l = (2 : ℚ) ^ (-k + k') l := by
  obtain ⟨-, -, hm2, hmd⟩ := hm
  obtain ⟨-, hm'1, -, hm'd⟩ := hm'
  rw [val_gridQuotient h h',
    upperTri_mul_apply_diag (isUpperTri_mul hm2 (isUpperTri_twoDiag _)) hm'1,
    upperTri_mul_apply_diag hm2 (isUpperTri_twoDiag _), (hmd l).2, (hm'd l).1, one_mul,
    mul_one, twoDiag, Matrix.diagonal_apply_eq]

/-- **Integrality of grid quotients.**  If `b, b'` are grid points and the
diagonal of `b'⁻¹ b` is bounded by `2^E`, then `2^E · b⁻¹ b'` is integral. -/
theorem isIntegral_pow_smul_gridQuotient {b b' : Matˣ} (hb : IsGridPoint b)
    (hb' : IsGridPoint b') (E : ℕ)
    (hE : ∀ l, ((b'⁻¹ * b : Matˣ) : Mat) l l ≤ (2 : ℚ) ^ E) :
    IsIntegral ((2 : ℚ) ^ E • ((b⁻¹ * b' : Matˣ) : Mat)) := by
  obtain ⟨k, m, hm, h⟩ := hb
  obtain ⟨k', m', hm', h'⟩ := hb'
  have hd : ∀ l, 0 ≤ (E : ℤ) + (-k + k') l := by
    intro l
    have hle : (2 : ℚ) ^ (-k' + k) l ≤ (2 : ℚ) ^ (E : ℤ) := by
      rw [← gridQuotient_apply_diag hm' hm h' h l, zpow_natCast]
      exact hE l
    have hle' : (-k' + k) l ≤ (E : ℤ) :=
      (zpow_le_zpow_iff_right₀ (one_lt_two : (1 : ℚ) < 2)).mp hle
    have h1 : -k' l + k l ≤ (E : ℤ) := hle'
    show 0 ≤ (E : ℤ) + (-k l + k' l)
    linarith
  have hsmul : (2 : ℚ) ^ E • (((m⁻¹ : Matˣ) : Mat) * twoDiag (-k + k') * (m' : Mat)) =
      ((m⁻¹ : Matˣ) : Mat) * ((2 : ℚ) ^ E • twoDiag (-k + k')) * (m' : Mat) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [val_gridQuotient h h', hsmul]
  exact isIntegral_mul (isIntegral_mul hm.1.2 (isIntegral_pow_smul_twoDiag E _ hd)) hm'.1.1

end GroupApproximation.Full.NN09b
