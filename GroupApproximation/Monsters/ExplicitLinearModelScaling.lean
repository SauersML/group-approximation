import GroupApproximation.Monsters.ExplicitLinearModel

/-!
# The scaling family of linear models

`ExplicitLinearModel` fixes the doubling matrix `D = diag(2,2,2,1)`.  Nothing
in the affine picture singles out the exponent `2`: for every `m` the matrix
`D_m = diag(m,m,m,1)` commutes with the rotation block and multiplies each
translation generator by `m`, and for `m ≥ 2` the marked translation `v₁`
again escapes the conjugated copy because `D_m⁻¹ v₁ D_m` has the entry `1/m`.

This file records that family.  The six affine generators, the subgroup
`gammaBar` they generate, and its integrality invariant are all reused from
`ExplicitLinearModel` unchanged -- only the scaling matrix moves.  The
outputs consumed downstream are

* `conjScale m`, an endomorphism of `gammaBar` for `m ≠ 0`;
* `conjScale_injective`, its injectivity; and
* `v1G_not_mem_range_conjScale`, the escape of the marked generator for
  `m ≥ 2`.

Two devices keep the symbolic exponent cheap.  The scaling matrices are
`Matrix.diagonal`s, so `diagonal_mul` and `mul_diagonal` replace every
sixteen-term matrix product by a pointwise scalar identity; and the three
translation generators are instances of one three-parameter family `transM`,
whose powers are computed once by induction instead of once per generator.
-/

namespace GroupApproximation
namespace ExplicitLinearModelScaling

open Matrix ExplicitLinearModel

/-! ## The affine translation family -/

/-- The affine translation by the vector `(a,b,c)`. -/
def transM (a b c : ℚ) : Mat := !![1,0,0,a; 0,1,0,b; 0,0,1,c; 0,0,0,1]

theorem transM_zero : transM 0 0 0 = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> norm_num [transM, Matrix.one_apply] <;> decide

theorem transM_mul (a b c a' b' c' : ℚ) :
    transM a b c * transM a' b' c' = transM (a + a') (b + b') (c + c') := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [transM, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem transM_pow (a b c : ℚ) (n : ℕ) :
    transM a b c ^ n = transM (n * a) (n * b) (n * c) := by
  induction n with
  | zero => simpa using transM_zero.symm
  | succ n ih =>
      rw [pow_succ, ih, transM_mul]
      congr 1 <;> push_cast <;> ring

@[simp] theorem v1M_eq : v1M = transM 1 0 0 := rfl
@[simp] theorem v2M_eq : v2M = transM 0 1 0 := rfl
@[simp] theorem v3M_eq : v3M = transM 0 0 1 := rfl

/-! ## The scaling matrices -/

/-- The diagonal of the scaling matrix `D_m = diag(m,m,m,1)`. -/
def scaleDiag (m : ℕ) : Fin 4 → ℚ := ![(m : ℚ), (m : ℚ), (m : ℚ), 1]

/-- The scaling matrix `D_m = diag(m,m,m,1)`. -/
def dScaleM (m : ℕ) : Mat := Matrix.diagonal (scaleDiag m)

/-- The inverse scaling matrix `diag(1/m,1/m,1/m,1)`. -/
def dScaleInvM (m : ℕ) : Mat :=
  Matrix.diagonal (fun i => (scaleDiag m i)⁻¹)

theorem scaleDiag_ne_zero {m : ℕ} (hm : m ≠ 0) (i : Fin 4) :
    scaleDiag m i ≠ 0 := by
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  fin_cases i
  · simpa [scaleDiag] using hmQ
  · simpa [scaleDiag] using hmQ
  · simpa [scaleDiag] using hmQ
  · simp [scaleDiag]

theorem dScaleM_mul_inv {m : ℕ} (hm : m ≠ 0) :
    dScaleM m * dScaleInvM m = 1 := by
  rw [dScaleM, dScaleInvM, Matrix.diagonal_mul_diagonal]
  rw [show (fun i => scaleDiag m i * (scaleDiag m i)⁻¹) = fun _ : Fin 4 => (1 : ℚ) from
    funext fun i => mul_inv_cancel₀ (scaleDiag_ne_zero hm i)]
  exact Matrix.diagonal_one

theorem dScaleInvM_mul {m : ℕ} (hm : m ≠ 0) :
    dScaleInvM m * dScaleM m = 1 := by
  rw [dScaleM, dScaleInvM, Matrix.diagonal_mul_diagonal]
  rw [show (fun i => (scaleDiag m i)⁻¹ * scaleDiag m i) = fun _ : Fin 4 => (1 : ℚ) from
    funext fun i => inv_mul_cancel₀ (scaleDiag_ne_zero hm i)]
  exact Matrix.diagonal_one

/-- `D_m` as a unit of the matrix ring. -/
def dScaleU (m : ℕ) (hm : m ≠ 0) : Matˣ :=
  ⟨dScaleM m, dScaleInvM m, dScaleM_mul_inv hm, dScaleInvM_mul hm⟩

/-! ## Commutation with the six affine generators

Because `D_m` is diagonal, an identity `D_m · A = B · D_m` is the pointwise
scalar statement `d i · A i j = B i j · d j`; no matrix product is ever
expanded. -/

theorem dScale_comm_of {A B : Mat} (m : ℕ)
    (h : ∀ i j, scaleDiag m i * A i j = B i j * scaleDiag m j) :
    dScaleM m * A = B * dScaleM m := by
  refine Matrix.ext fun i j => ?_
  rw [dScaleM, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact h i j

theorem dScale_comm_trans (m : ℕ) (a b c : ℚ) :
    dScaleM m * transM a b c =
      transM ((m : ℚ) * a) ((m : ℚ) * b) ((m : ℚ) * c) * dScaleM m := by
  refine dScale_comm_of m fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [transM, scaleDiag, Matrix.vecHead, Matrix.vecTail]

theorem dScale_comm_x (m : ℕ) : dScaleM m * xM = xM * dScaleM m := by
  refine dScale_comm_of m fun i j => ?_
  fin_cases i <;> fin_cases j <;> norm_num [xM, scaleDiag, Matrix.vecHead, Matrix.vecTail]

theorem dScale_comm_y (m : ℕ) : dScaleM m * yM = yM * dScaleM m := by
  refine dScale_comm_of m fun i j => ?_
  fin_cases i <;> fin_cases j <;> norm_num [yM, scaleDiag, Matrix.vecHead, Matrix.vecTail]

theorem dScale_comm_z (m : ℕ) : dScaleM m * zM = zM * dScaleM m := by
  refine dScale_comm_of m fun i j => ?_
  fin_cases i <;> fin_cases j <;> norm_num [zM, scaleDiag, Matrix.vecHead, Matrix.vecTail]

/-- The scaling matrix multiplies a translation generator by `m`. -/
theorem dScale_comm_pow (m : ℕ) (a b c : ℚ) :
    dScaleM m * transM a b c = transM a b c ^ m * dScaleM m := by
  rw [transM_pow]
  exact dScale_comm_trans m a b c

theorem dScale_comm_v1 (m : ℕ) : dScaleM m * v1M = v1M ^ m * dScaleM m :=
  dScale_comm_pow m 1 0 0

theorem dScale_comm_v2 (m : ℕ) : dScaleM m * v2M = v2M ^ m * dScaleM m :=
  dScale_comm_pow m 0 1 0

theorem dScale_comm_v3 (m : ℕ) : dScaleM m * v3M = v3M ^ m * dScaleM m :=
  dScale_comm_pow m 0 0 1

/-! ## The scaling conjugation on the base subgroup -/

variable {m : ℕ}

theorem dScaleU_conj_fixed (hm : m ≠ 0) {u : Matˣ} {A : Mat}
    (hu : (u : Mat) = A) (hA : dScaleM m * A = A * dScaleM m) :
    dScaleU m hm * u * (dScaleU m hm)⁻¹ = u := by
  apply Units.ext
  change dScaleM m * (u : Mat) * dScaleInvM m = (u : Mat)
  rw [hu, hA, mul_assoc, dScaleM_mul_inv hm, mul_one]

theorem dScaleU_conj_pow (hm : m ≠ 0) {u : Matˣ} {A : Mat}
    (hu : (u : Mat) = A) (hA : dScaleM m * A = A ^ m * dScaleM m) :
    dScaleU m hm * u * (dScaleU m hm)⁻¹ = u ^ m := by
  apply Units.ext
  change dScaleM m * (u : Mat) * dScaleInvM m = ((u ^ m : Matˣ) : Mat)
  rw [Units.val_pow_eq_pow_val, hu, hA, mul_assoc, dScaleM_mul_inv hm, mul_one]

theorem dScaleU_conj_xU (hm : m ≠ 0) :
    dScaleU m hm * xU * (dScaleU m hm)⁻¹ = xU :=
  dScaleU_conj_fixed hm rfl (dScale_comm_x m)

theorem dScaleU_conj_yU (hm : m ≠ 0) :
    dScaleU m hm * yU * (dScaleU m hm)⁻¹ = yU :=
  dScaleU_conj_fixed hm rfl (dScale_comm_y m)

theorem dScaleU_conj_zU (hm : m ≠ 0) :
    dScaleU m hm * zU * (dScaleU m hm)⁻¹ = zU :=
  dScaleU_conj_fixed hm rfl (dScale_comm_z m)

theorem dScaleU_conj_v1U (hm : m ≠ 0) :
    dScaleU m hm * v1U * (dScaleU m hm)⁻¹ = v1U ^ m :=
  dScaleU_conj_pow hm rfl (dScale_comm_v1 m)

theorem dScaleU_conj_v2U (hm : m ≠ 0) :
    dScaleU m hm * v2U * (dScaleU m hm)⁻¹ = v2U ^ m :=
  dScaleU_conj_pow hm rfl (dScale_comm_v2 m)

theorem dScaleU_conj_v3U (hm : m ≠ 0) :
    dScaleU m hm * v3U * (dScaleU m hm)⁻¹ = v3U ^ m :=
  dScaleU_conj_pow hm rfl (dScale_comm_v3 m)

theorem dScaleU_conj_mem (hm : m ≠ 0) {u : Matˣ} (hu : u ∈ gammaBar) :
    dScaleU m hm * u * (dScaleU m hm)⁻¹ ∈ gammaBar := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
      rcases hu with h | h | h | h | h | h
      · subst h; rw [dScaleU_conj_xU hm]; exact Subgroup.subset_closure (by simp)
      · subst h; rw [dScaleU_conj_yU hm]; exact Subgroup.subset_closure (by simp)
      · subst h; rw [dScaleU_conj_zU hm]; exact Subgroup.subset_closure (by simp)
      · subst h; rw [dScaleU_conj_v1U hm]
        exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) m
      · subst h; rw [dScaleU_conj_v2U hm]
        exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) m
      · subst h; rw [dScaleU_conj_v3U hm]
        exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) m
  | one => simp
  | mul u v _ _ hu hv =>
      have h : dScaleU m hm * (u * v) * (dScaleU m hm)⁻¹ =
          (dScaleU m hm * u * (dScaleU m hm)⁻¹) *
            (dScaleU m hm * v * (dScaleU m hm)⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ hu hv
  | inv u _ hu =>
      have h : dScaleU m hm * u⁻¹ * (dScaleU m hm)⁻¹ =
          (dScaleU m hm * u * (dScaleU m hm)⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ hu

/-- Conjugation by `D_m` as an endomorphism of the affine base subgroup. -/
def conjScale (m : ℕ) (hm : m ≠ 0) : gammaBar →* gammaBar where
  toFun u := ⟨dScaleU m hm * u * (dScaleU m hm)⁻¹, dScaleU_conj_mem hm u.2⟩
  map_one' := by
    apply Subtype.ext
    change dScaleU m hm * 1 * (dScaleU m hm)⁻¹ = 1
    group
  map_mul' u v := Subtype.ext (by
    show dScaleU m hm * (↑u * ↑v) * (dScaleU m hm)⁻¹ =
      (dScaleU m hm * ↑u * (dScaleU m hm)⁻¹) *
        (dScaleU m hm * ↑v * (dScaleU m hm)⁻¹)
    group)

theorem conjScale_injective (hm : m ≠ 0) :
    Function.Injective (conjScale m hm) := by
  intro u v h
  have h' : dScaleU m hm * (u : Matˣ) * (dScaleU m hm)⁻¹ =
      dScaleU m hm * (v : Matˣ) * (dScaleU m hm)⁻¹ := congrArg Subtype.val h
  exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))

@[simp] theorem conjScale_apply (hm : m ≠ 0) (u : gammaBar) :
    ((conjScale m hm u : gammaBar) : Matˣ) =
      dScaleU m hm * (u : Matˣ) * (dScaleU m hm)⁻¹ := rfl

theorem conjScale_v1G (hm : m ≠ 0) : conjScale m hm v1G = v1G ^ m := by
  apply Subtype.ext
  rw [conjScale_apply hm]
  simpa [v1G] using dScaleU_conj_v1U (m := m) hm

theorem conjScale_v2G (hm : m ≠ 0) : conjScale m hm v2G = v2G ^ m := by
  apply Subtype.ext
  rw [conjScale_apply hm]
  simpa [v2G] using dScaleU_conj_v2U (m := m) hm

theorem conjScale_v3G (hm : m ≠ 0) : conjScale m hm v3G = v3G ^ m := by
  apply Subtype.ext
  rw [conjScale_apply hm]
  simpa [v3G] using dScaleU_conj_v3U (m := m) hm

theorem conjScale_xG (hm : m ≠ 0) : conjScale m hm xG = xG := by
  apply Subtype.ext
  rw [conjScale_apply hm]
  simpa [xG] using dScaleU_conj_xU (m := m) hm

theorem conjScale_yG (hm : m ≠ 0) : conjScale m hm yG = yG := by
  apply Subtype.ext
  rw [conjScale_apply hm]
  simpa [yG] using dScaleU_conj_yU (m := m) hm

theorem conjScale_zG (hm : m ≠ 0) : conjScale m hm zG = zG := by
  apply Subtype.ext
  rw [conjScale_apply hm]
  simpa [zG] using dScaleU_conj_zU (m := m) hm

/-! ## The escape of the marked generator -/

/-- The moved marked generator has the non-integral entry `1/m`. -/
theorem dScaleInv_v1_dScale_entry (m : ℕ) :
    (dScaleInvM m * v1M * dScaleM m) 0 3 = ((m : ℚ))⁻¹ := by
  rw [dScaleM, dScaleInvM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  norm_num [v1M, scaleDiag, Matrix.cons_val_three, Matrix.cons_val_two,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail]

/-- **The marked generator escapes the scaled copy** for every `m ≥ 2`: a
preimage would be the matrix `D_m⁻¹ v₁ D_m`, whose `(0,3)` entry is `1/m`,
while every element of `gammaBar` has integer entries. -/
theorem v1G_not_mem_range_conjScale {m : ℕ} (hm0 : m ≠ 0) (hm : 2 ≤ m) :
    v1G ∉ Set.range (conjScale m hm0) := by
  rintro ⟨g, hg⟩
  have hval : dScaleU m hm0 * (g : Matˣ) * (dScaleU m hm0)⁻¹ = v1U :=
    Subtype.ext_iff.mp hg
  have hgval : (g : Matˣ) = (dScaleU m hm0)⁻¹ * v1U * dScaleU m hm0 := by
    rw [← hval]; group
  have hint : IsIntegral ((g : Matˣ) : Mat) := (gammaBar_isIntegralUnit g.2).1
  rw [hgval] at hint
  have hentry :
      ((((dScaleU m hm0)⁻¹ * v1U * dScaleU m hm0 : Matˣ) : Mat)) 0 3 =
        ((m : ℚ))⁻¹ := by
    show (dScaleInvM m * v1M * dScaleM m) 0 3 = ((m : ℚ))⁻¹
    exact dScaleInv_v1_dScale_entry m
  obtain ⟨k, hk⟩ := hint 0 3
  rw [hentry] at hk
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hmk : ((m * k : ℤ) : ℚ) = 1 := by
    have hk' : (k : ℚ) = ((m : ℚ))⁻¹ := by exact_mod_cast hk
    push_cast
    rw [hk']
    exact mul_inv_cancel₀ hmQ
  have hmul : (m : ℤ) * k = 1 := by exact_mod_cast hmk
  have hdvd : (m : ℤ) ∣ 1 := ⟨k, hmul.symm⟩
  have hle : (m : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  omega

/-- The structural package of the scaling family: for every `m ≥ 2`,
conjugation by `D_m` is an injective endomorphism of the affine base subgroup
whose range misses the marked translation. -/
theorem scaling_linear_model_package {m : ℕ} (hm0 : m ≠ 0) (hm : 2 ≤ m) :
    Function.Injective (conjScale m hm0) ∧
      v1G ∉ Set.range (conjScale m hm0) :=
  ⟨conjScale_injective hm0, v1G_not_mem_range_conjScale hm0 hm⟩

end ExplicitLinearModelScaling
end GroupApproximation
