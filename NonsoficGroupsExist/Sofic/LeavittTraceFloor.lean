import NonsoficGroupsExist.Sofic.PhasePropagation

/-!
# A dimension-free Hilbert--Schmidt floor for the Leavitt relations

Four square matrices cannot approximately satisfy even the three diagonal
binary Leavitt relations in normalized Hilbert--Schmidt norm.  If

`A₀ = T₀S₀ - 1`, `A₁ = T₁S₁ - 1`, and
`C = S₀T₀ + S₁T₁ - 1`,

then cyclicity of the normalized matrix trace gives

`τ(C) = τ(A₀) + τ(A₁) + 1`.

The internally proved trace Cauchy--Schwarz inequality
`|τ(X)| ≤ |X|₂` therefore forces

`1 ≤ |A₀|₂ + |A₁|₂ + |C|₂`.

In particular one of the three defects is at least `1 / 3`, independently of
the matrix dimension and without any operator-norm or adjoint hypothesis.
-/

namespace NonsoficGroupsExist

open Matrix

/-- The normalized Hilbert--Schmidt norm associated to `hsNormSq`. -/
noncomputable def hsNorm (Y : FiniteModel) (A : Matrix Y Y ℂ) : ℝ :=
  Real.sqrt (hsNormSq Y A)

theorem hsNorm_nonneg (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    0 ≤ hsNorm Y A :=
  Real.sqrt_nonneg _

/-- The normalized trace is dominated by the normalized Hilbert--Schmidt
norm.  This is the square-root form of
`normSq_normTrace_le_hsNormSq`. -/
theorem norm_normTrace_le_hsNorm (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    ‖normTrace Y A‖ ≤ hsNorm Y A := by
  have h := Real.sqrt_le_sqrt (normSq_normTrace_le_hsNormSq Y A)
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] at h
  exact h

/-- Cyclicity of matrix trace rewrites the coisometry defect as the two
isometry defects plus one. -/
theorem normTrace_leavitt_defect_identity (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (S₀ S₁ T₀ T₁ : Matrix Y Y ℂ) :
    normTrace Y (S₀ * T₀ + S₁ * T₁ - 1) =
      normTrace Y (T₀ * S₀ - 1) + normTrace Y (T₁ * S₁ - 1) + 1 := by
  have hc : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hY.ne'
  unfold normTrace
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm S₀ T₀, Matrix.trace_mul_comm S₁ T₁,
    Matrix.trace_one]
  field_simp
  ring

/-- **Normalized-HS Leavitt trace floor.**  The sum of the three diagonal
binary Leavitt defects is at least one in every nonzero finite matrix
algebra. -/
theorem one_le_sum_leavitt_hsNorm (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (S₀ S₁ T₀ T₁ : Matrix Y Y ℂ) :
    1 ≤ hsNorm Y (T₀ * S₀ - 1) + hsNorm Y (T₁ * S₁ - 1) +
      hsNorm Y (S₀ * T₀ + S₁ * T₁ - 1) := by
  let A₀ := T₀ * S₀ - 1
  let A₁ := T₁ * S₁ - 1
  let C := S₀ * T₀ + S₁ * T₁ - 1
  have htrace : normTrace Y C = normTrace Y A₀ + normTrace Y A₁ + 1 :=
    normTrace_leavitt_defect_identity Y hY S₀ S₁ T₀ T₁
  have hone : (1 : ℂ) = normTrace Y C - normTrace Y A₀ - normTrace Y A₁ := by
    rw [htrace]
    ring
  calc
    (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
    _ = ‖normTrace Y C - normTrace Y A₀ - normTrace Y A₁‖ := by rw [← hone]
    _ ≤ ‖normTrace Y C‖ + ‖normTrace Y A₀‖ + ‖normTrace Y A₁‖ := by
      calc
        ‖normTrace Y C - normTrace Y A₀ - normTrace Y A₁‖ ≤
            ‖normTrace Y C - normTrace Y A₀‖ + ‖normTrace Y A₁‖ :=
          norm_sub_le _ _
        _ ≤ (‖normTrace Y C‖ + ‖normTrace Y A₀‖) +
            ‖normTrace Y A₁‖ :=
          add_le_add_right (norm_sub_le _ _) _
    _ ≤ hsNorm Y C + hsNorm Y A₀ + hsNorm Y A₁ := by
      gcongr <;> exact norm_normTrace_le_hsNorm _ _
    _ = hsNorm Y A₀ + hsNorm Y A₁ + hsNorm Y C := by ring

/-- **Sharp one-third obstruction.**  At least one of the three diagonal
binary Leavitt relations has normalized Hilbert--Schmidt defect at least
`1 / 3`. -/
theorem one_third_le_max_leavitt_hsNorm (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (S₀ S₁ T₀ T₁ : Matrix Y Y ℂ) :
    (1 / 3 : ℝ) ≤
      max (hsNorm Y (T₀ * S₀ - 1))
        (max (hsNorm Y (T₁ * S₁ - 1))
          (hsNorm Y (S₀ * T₀ + S₁ * T₁ - 1))) := by
  let e₀ := hsNorm Y (T₀ * S₀ - 1)
  let e₁ := hsNorm Y (T₁ * S₁ - 1)
  let eC := hsNorm Y (S₀ * T₀ + S₁ * T₁ - 1)
  let M := max e₀ (max e₁ eC)
  have hsum : 1 ≤ e₀ + e₁ + eC :=
    one_le_sum_leavitt_hsNorm Y hY S₀ S₁ T₀ T₁
  have he₀ : e₀ ≤ M := le_max_left _ _
  have he₁ : e₁ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have heC : eC ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  change (1 / 3 : ℝ) ≤ M
  linarith

end NonsoficGroupsExist
