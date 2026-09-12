import GroupApproximation.Sofic.PhasePropagation
import GroupApproximation.Sofic.NormTraceGap
import Mathlib.Analysis.Matrix.Order

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

namespace GroupApproximation

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder

/-- The normalized Hilbert--Schmidt norm associated to `hsNormSq`. -/
noncomputable def hsNorm (Y : FiniteModel) (A : Matrix Y Y ℂ) : ℝ :=
  Real.sqrt (hsNormSq Y A)

theorem hsNorm_nonneg (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    0 ≤ hsNorm Y A :=
  Real.sqrt_nonneg _

/-- Scalar mass-saturation estimate used by the diagonal-pairing argument.
If two successive contractions have masses `x` and `y`, both bounded by the
original mass `w`, and the final mass is within `η` of `w`, then the total
squared mass loss is at most `2η`. -/
theorem contraction_sq_mass_loss_le_two
    (x y w η : ℝ)
    (hy : 0 ≤ y) (hyx : y ≤ x) (hxw : x ≤ w) (hw : w ≤ 1)
    (hη : 0 ≤ η) (hclose : w ≤ y + η) :
    x ^ 2 - y ^ 2 ≤ 2 * η := by
  have hdiff0 : 0 ≤ x - y := sub_nonneg.mpr hyx
  have hdiff : x - y ≤ η := by linarith
  have hsum0 : 0 ≤ x + y := add_nonneg (hy.trans hyx) hy
  have hsum : x + y ≤ 2 := by linarith
  calc
    x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
    _ ≤ η * 2 := mul_le_mul hdiff hsum hsum0 hη
    _ = 2 * η := by ring

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
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right
                (norm_sub_le (normTrace Y C) (normTrace Y A₀))
                ‖normTrace Y A₁‖
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

/-! ## A multiplicative-only Leavitt floor -/

/-- Left multiplication by an arbitrary matrix costs at most its squared
operator norm in normalized Hilbert--Schmidt norm. -/
theorem hsNormSq_mul_le_sq_l2_opNorm_mul (Y : FiniteModel)
    (A B : Matrix Y Y ℂ) :
    hsNormSq Y (A * B) ≤ ‖A‖ ^ 2 * hsNormSq Y B := by
  classical
  have hcol : ∀ j : Y,
      ∑ i : Y, Complex.normSq ((A * B) i j) ≤
        ‖A‖ ^ 2 * ∑ i : Y, Complex.normSq (B i j) := by
    intro j
    simpa only [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum] using
      (sum_normSq_mulVec_le Y A (fun i ↦ B i j))
  unfold hsNormSq
  rw [Finset.sum_comm]
  calc
    (∑ j : Y, ∑ i : Y, Complex.normSq ((A * B) i j)) /
          Fintype.card Y
        ≤ (∑ j : Y, ‖A‖ ^ 2 * ∑ i : Y, Complex.normSq (B i j)) /
          Fintype.card Y := by
            exact div_le_div_of_nonneg_right
              (Finset.sum_le_sum fun j _ ↦ hcol j) (Nat.cast_nonneg _)
    _ = ‖A‖ ^ 2 *
          ((∑ i : Y, ∑ j : Y, Complex.normSq (B i j)) /
            Fintype.card Y) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          ring

/-- Right multiplication by an arbitrary matrix costs at most its squared
operator norm in normalized Hilbert--Schmidt norm. -/
theorem hsNormSq_mul_le_sq_l2_opNorm_right (Y : FiniteModel)
    (A B : Matrix Y Y ℂ) :
    hsNormSq Y (A * B) ≤ ‖B‖ ^ 2 * hsNormSq Y A := by
  calc
    hsNormSq Y (A * B) = hsNormSq Y ((A * B)ᴴ) :=
      (hsNormSq_conjTranspose Y (A * B)).symm
    _ = hsNormSq Y (Bᴴ * Aᴴ) := by rw [Matrix.conjTranspose_mul]
    _ ≤ ‖Bᴴ‖ ^ 2 * hsNormSq Y Aᴴ :=
      hsNormSq_mul_le_sq_l2_opNorm_mul Y Bᴴ Aᴴ
    _ = ‖B‖ ^ 2 * hsNormSq Y A := by
      rw [Matrix.l2_opNorm_conjTranspose, hsNormSq_conjTranspose]

/-- **Two-sided transition control.**  Forward and reverse intertwining
defects control the commutator of the source arrow with the transition Gram
operator.  Unlike the one-sided theorem below, this statement does not
require either arrow to be unitary. -/
theorem hsNormSq_transitionGram_commutator_le_two_sided
    (Y : FiniteModel) (T A B : Matrix Y Y ℂ)
    (hT : ‖T‖ ≤ 1) :
    hsNormSq Y ((Tᴴ * T) * A - A * (Tᴴ * T)) ≤
      2 * hsNormSq Y (T * A - B * T) +
        2 * hsNormSq Y (Tᴴ * B - A * Tᴴ) := by
  let Eforward := T * A - B * T
  let Ereversed := Tᴴ * B - A * Tᴴ
  have hTstar : ‖Tᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hT
  have hforward :
      hsNormSq Y (Tᴴ * Eforward) ≤ hsNormSq Y Eforward := by
    have hTstarSq : ‖Tᴴ‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg Tᴴ]
    calc
      hsNormSq Y (Tᴴ * Eforward) ≤
          ‖Tᴴ‖ ^ 2 * hsNormSq Y Eforward :=
        hsNormSq_mul_le_sq_l2_opNorm_mul Y Tᴴ Eforward
      _ ≤ 1 * hsNormSq Y Eforward :=
        mul_le_mul_of_nonneg_right hTstarSq
          (hsNormSq_nonneg Y Eforward)
      _ = hsNormSq Y Eforward := one_mul _
  have hreversed :
      hsNormSq Y (Ereversed * T) ≤ hsNormSq Y Ereversed := by
    have hTSq : ‖T‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg T]
    calc
      hsNormSq Y (Ereversed * T) ≤
          ‖T‖ ^ 2 * hsNormSq Y Ereversed :=
        hsNormSq_mul_le_sq_l2_opNorm_right Y Ereversed T
      _ ≤ 1 * hsNormSq Y Ereversed :=
        mul_le_mul_of_nonneg_right hTSq
          (hsNormSq_nonneg Y Ereversed)
      _ = hsNormSq Y Ereversed := one_mul _
  have hfactor :
      (Tᴴ * T) * A - A * (Tᴴ * T) =
        Tᴴ * Eforward + Ereversed * T := by
    dsimp [Eforward, Ereversed]
    noncomm_ring
  rw [hfactor]
  calc
    hsNormSq Y (Tᴴ * Eforward + Ereversed * T) ≤
        2 * hsNormSq Y (Tᴴ * Eforward) +
          2 * hsNormSq Y (Ereversed * T) :=
      hsNormSq_add_le Y _ _
    _ ≤ 2 * hsNormSq Y Eforward + 2 * hsNormSq Y Ereversed := by
      linarith
    _ = 2 * hsNormSq Y (T * A - B * T) +
        2 * hsNormSq Y (Tᴴ * B - A * Tᴴ) := by
      rfl

/-- **Transition-Gram control.**  If a contraction `T` approximately
intertwines a source unitary `A` with a target unitary `B`, then its Gram
operator `Tᴴ * T` approximately commutes with `A`.  The estimate is
dimension-free and is the algebraic input to spectral coarea. -/
theorem hsNormSq_transitionGram_commutator_le_four
    (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (T A B : Matrix Y Y ℂ)
    (hT : ‖T‖ ≤ 1)
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) :
    hsNormSq Y ((Tᴴ * T) * A - A * (Tᴴ * T)) ≤
      4 * hsNormSq Y (T * A - B * T) := by
  let X := T * A
  let Z := B * T
  let E := X - Z
  have hAstar : Aᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hA
  have hAA : Aᴴ * A = 1 := Unitary.star_mul_self_of_mem hA
  have hBB : Bᴴ * B = 1 := Unitary.star_mul_self_of_mem hB
  have hX : ‖X‖ ≤ 1 := by
    dsimp [X]
    rw [CStarRing.norm_mul_mem_unitary _ hA]
    exact hT
  have hZ : ‖Z‖ ≤ 1 := by
    dsimp [Z]
    rw [CStarRing.norm_mem_unitary_mul _ hB]
    exact hT
  have hXstar : ‖Xᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hX
  have hleft : hsNormSq Y (Xᴴ * E) ≤ hsNormSq Y E := by
    have hXstarSq : ‖Xᴴ‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg Xᴴ]
    calc
      hsNormSq Y (Xᴴ * E) ≤ ‖Xᴴ‖ ^ 2 * hsNormSq Y E :=
        hsNormSq_mul_le_sq_l2_opNorm_mul Y Xᴴ E
      _ ≤ 1 * hsNormSq Y E :=
        mul_le_mul_of_nonneg_right hXstarSq (hsNormSq_nonneg Y E)
      _ = hsNormSq Y E := one_mul _
  have hright : hsNormSq Y (Eᴴ * Z) ≤ hsNormSq Y E := by
    have hZSq : ‖Z‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg Z]
    calc
      hsNormSq Y (Eᴴ * Z) ≤ ‖Z‖ ^ 2 * hsNormSq Y Eᴴ :=
        hsNormSq_mul_le_sq_l2_opNorm_right Y Eᴴ Z
      _ = ‖Z‖ ^ 2 * hsNormSq Y E := by
        rw [hsNormSq_conjTranspose]
      _ ≤ 1 * hsNormSq Y E :=
        mul_le_mul_of_nonneg_right hZSq (hsNormSq_nonneg Y E)
      _ = hsNormSq Y E := one_mul _
  have hXX : Xᴴ * X = Aᴴ * (Tᴴ * T) * A := by
    dsimp [X]
    rw [Matrix.conjTranspose_mul]
    noncomm_ring
  have hZZ : Zᴴ * Z = Tᴴ * T := by
    dsimp [Z]
    rw [Matrix.conjTranspose_mul]
    calc
      (Tᴴ * Bᴴ) * (B * T) = Tᴴ * (Bᴴ * B) * T := by
        noncomm_ring
      _ = Tᴴ * T := by rw [hBB, Matrix.mul_one]
  have hfactor :
      Aᴴ * ((Tᴴ * T) * A - A * (Tᴴ * T)) =
        Xᴴ * E + Eᴴ * Z := by
    calc
      Aᴴ * ((Tᴴ * T) * A - A * (Tᴴ * T)) =
          Aᴴ * (Tᴴ * T) * A - Tᴴ * T := by
            rw [Matrix.mul_sub]
            rw [← Matrix.mul_assoc Aᴴ A (Tᴴ * T), hAA, Matrix.one_mul]
            simp only [Matrix.mul_assoc]
      _ = Xᴴ * X - Zᴴ * Z := by rw [hXX, hZZ]
      _ = Xᴴ * E + Eᴴ * Z := by
        dsimp [E]
        rw [Matrix.conjTranspose_sub]
        noncomm_ring
  have hinvariant :
      hsNormSq Y ((Tᴴ * T) * A - A * (Tᴴ * T)) =
        hsNormSq Y (Aᴴ * ((Tᴴ * T) * A - A * (Tᴴ * T))) := by
    symm
    exact hsNormSq_mul_left Y hAstar hY _
  rw [hinvariant, hfactor]
  calc
    hsNormSq Y (Xᴴ * E + Eᴴ * Z) ≤
        2 * hsNormSq Y (Xᴴ * E) + 2 * hsNormSq Y (Eᴴ * Z) :=
      hsNormSq_add_le Y _ _
    _ ≤ 4 * hsNormSq Y E := by linarith
    _ = 4 * hsNormSq Y (T * A - B * T) := by
      rfl

/-- A diagonal pairing defect decomposes into the desired forward
transition and one range-deficiency term.  Positivity of the latter supplies
the square-root estimate recorded in the accompanying research note. -/
theorem pairing_defect_transition_decomposition
    (Y : FiniteModel) (W L R : Matrix Y Y ℂ) :
    W * L - R * W =
      R * (Rᴴ * W * L - W) + (1 - R * Rᴴ) * (W * L) := by
  noncomm_ring

/-- Squared-HS propagation through
`pairing_defect_transition_decomposition`.  The remaining hypothesis is
exactly the positive range-deficiency estimate supplied by mass saturation. -/
theorem hsNormSq_pairing_transition_le_of_range_deficiency
    (Y : FiniteModel) (W L R : Matrix Y Y ℂ) (κ : ℝ)
    (hR : ‖R‖ ≤ 1)
    (hdeficiency :
      hsNormSq Y ((1 - R * Rᴴ) * (W * L)) ≤ κ) :
    hsNormSq Y (W * L - R * W) ≤
      2 * hsNormSq Y (Rᴴ * W * L - W) + 2 * κ := by
  let D := Rᴴ * W * L - W
  have hRSq : ‖R‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg R]
  have hDnonneg : 0 ≤ hsNormSq Y D := hsNormSq_nonneg Y D
  have hRD : hsNormSq Y (R * D) ≤ hsNormSq Y D := by
    calc
      hsNormSq Y (R * D) ≤ ‖R‖ ^ 2 * hsNormSq Y D :=
        hsNormSq_mul_le_sq_l2_opNorm_mul Y R D
      _ ≤ 1 * hsNormSq Y D :=
        mul_le_mul_of_nonneg_right hRSq hDnonneg
      _ = hsNormSq Y D := one_mul _
  rw [pairing_defect_transition_decomposition]
  calc
    hsNormSq Y
        (R * (Rᴴ * W * L - W) + (1 - R * Rᴴ) * (W * L)) ≤
        2 * hsNormSq Y (R * (Rᴴ * W * L - W)) +
          2 * hsNormSq Y ((1 - R * Rᴴ) * (W * L)) :=
      hsNormSq_add_le Y _ _
    _ ≤ 2 * hsNormSq Y (Rᴴ * W * L - W) + 2 * κ := by
      dsimp [D] at hRD
      linarith

/-- A diagonal unitary pairing defect already controls the source Gram
commutator.  Thus spectral invariance is not a separate hypothesis once the
two diagonal pairing arrows have been repaired to unitaries. -/
theorem hsNormSq_pairing_defect_controls_sourceGram_commutator
    (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (W L R : Matrix Y Y ℂ)
    (hW : ‖W‖ ≤ 1)
    (hL : L ∈ Matrix.unitaryGroup Y ℂ)
    (hR : R ∈ Matrix.unitaryGroup Y ℂ) :
    hsNormSq Y ((Wᴴ * W) * L - L * (Wᴴ * W)) ≤
      4 * hsNormSq Y (Rᴴ * W * L - W) := by
  have hRRstar : R * Rᴴ = 1 := Unitary.mul_star_self_of_mem hR
  have hfactor :
      W * L - R * W = R * (Rᴴ * W * L - W) := by
    calc
      W * L - R * W = (R * Rᴴ) * W * L - R * W := by
        rw [hRRstar, Matrix.one_mul]
      _ = R * (Rᴴ * W * L - W) := by
        rw [Matrix.mul_sub]
        noncomm_ring
  have htransition :=
    hsNormSq_transitionGram_commutator_le_four
      Y hY W L R hW hL hR
  calc
    hsNormSq Y ((Wᴴ * W) * L - L * (Wᴴ * W)) ≤
        4 * hsNormSq Y (W * L - R * W) := htransition
    _ = 4 * hsNormSq Y (Rᴴ * W * L - W) := by
      rw [hfactor, hsNormSq_mul_left Y hR hY]

/-! ## Compression identities for an almost invariant carrier -/

/-- Inserting a carrier projection between two factors costs exactly one
one-sided leakage term.  This identity shows that only the left factor of a
Leavitt product needs carrier invariance. -/
theorem compressed_product_sub_carrier_identity
    (Y : FiniteModel) (P T S : Matrix Y Y ℂ) (hP : P * P = P) :
    P * T * P * S * P - P =
      P * (T * S - 1) * P - P * T * (1 - P) * S * P := by
  noncomm_ring [hP]

/-- Cross-product form of `compressed_product_sub_carrier_identity`. -/
theorem compressed_cross_product_identity
    (Y : FiniteModel) (P T S : Matrix Y Y ℂ) :
    P * T * P * S * P =
      P * (T * S) * P - P * T * (1 - P) * S * P := by
  noncomm_ring

/-- The normalized trace of a product of two positive semidefinite matrices
has nonnegative real part.  The product itself need not be self-adjoint. -/
theorem re_normTrace_mul_nonneg_of_posSemidef (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) {P Q : Matrix Y Y ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (normTrace Y (P * Q)).re := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  have hC' : P = Cᴴ * C := by
    simpa [Matrix.star_eq_conjTranspose] using hC
  have hpos : (C * Q * Cᴴ).PosSemidef := hQ.mul_mul_conjTranspose_same C
  have htrace : 0 ≤ (Matrix.trace (C * Q * Cᴴ)).re :=
    (RCLike.nonneg_iff.mp hpos.trace_nonneg).1
  have hcycle : Matrix.trace (P * Q) = Matrix.trace (C * Q * Cᴴ) := by
    rw [hC']
    calc
      Matrix.trace ((Cᴴ * C) * Q) = Matrix.trace (Cᴴ * (C * Q)) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace ((C * Q) * Cᴴ) := by
        exact Matrix.trace_mul_comm Cᴴ (C * Q)
      _ = Matrix.trace (C * Q * Cᴴ) := rfl
  have hcard : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  rw [normTrace, hcycle]
  simpa using div_nonneg htrace hcard.le

/-- A contraction has positive semidefinite Gram deficiency. -/
theorem one_sub_conjTranspose_mul_posSemidef_of_l2_opNorm_le_one
    (Y : FiniteModel) (A : Matrix Y Y ℂ) (hA : ‖A‖ ≤ 1) :
    (1 - Aᴴ * A).PosSemidef := by
  have hself (x : Y → ℂ) :
      star x ⬝ᵥ x = ((∑ i : Y, Complex.normSq (x i) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact Complex.normSq_eq_conj_mul_self.symm
  have hgram (x : Y → ℂ) :
      star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) =
        ((∑ i : Y, Complex.normSq ((A *ᵥ x) i) : ℝ) : ℂ) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_conjTranspose, star_star, hself]
  have hHerm : (1 - Aᴴ * A)ᴴ = 1 - Aᴴ * A := by simp
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun x ↦ ?_
  have hbound := sum_normSq_mulVec_le Y A x
  have hAsq : ‖A‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg A]
  have hxnonneg : 0 ≤ ∑ i : Y, Complex.normSq (x i) :=
    Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _
  have hreal :
      ∑ i : Y, Complex.normSq ((A *ᵥ x) i) ≤
        ∑ i : Y, Complex.normSq (x i) := by
    calc
      ∑ i : Y, Complex.normSq ((A *ᵥ x) i)
          ≤ ‖A‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) := hbound
      _ ≤ 1 * ∑ i : Y, Complex.normSq (x i) :=
        mul_le_mul_of_nonneg_right hAsq hxnonneg
      _ = ∑ i : Y, Complex.normSq (x i) := one_mul _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hself, hgram]
  exact RCLike.nonneg_iff.mpr ⟨sub_nonneg.mpr hreal, by simp⟩

/-- The positive range-deficiency estimate behind contraction mass
saturation.  For `Q=1-RRᴴ`, positivity of
`Q-Q²=R(1-RᴴR)Rᴴ` shows that applying `Q` costs no more squared HS mass than
was lost by applying `Rᴴ`. -/
theorem hsNormSq_range_deficiency_le_mass_loss
    (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (R X : Matrix Y Y ℂ) (hR : ‖R‖ ≤ 1) :
    hsNormSq Y ((1 - R * Rᴴ) * X) ≤
      hsNormSq Y X - hsNormSq Y (Rᴴ * X) := by
  let Q : Matrix Y Y ℂ := 1 - R * Rᴴ
  have hcore : (1 - Rᴴ * R).PosSemidef :=
    one_sub_conjTranspose_mul_posSemidef_of_l2_opNorm_le_one Y R hR
  have hQdiff : (Q - Q * Q).PosSemidef := by
    have hpos : (R * (1 - Rᴴ * R) * Rᴴ).PosSemidef :=
      hcore.mul_mul_conjTranspose_same R
    have hid : Q - Q * Q = R * (1 - Rᴴ * R) * Rᴴ := by
      dsimp [Q]
      noncomm_ring
    rw [hid]
    exact hpos
  have hweighted : (Xᴴ * (Q - Q * Q) * X).PosSemidef :=
    hQdiff.conjTranspose_mul_mul_same X
  have htraceNonneg :
      0 ≤ (Matrix.trace (Xᴴ * (Q - Q * Q) * X)).re :=
    (RCLike.nonneg_iff.mp hweighted.trace_nonneg).1
  have hQstar : Qᴴ = Q := by
    dsimp [Q]
    simp
  have hRtrace :
      Matrix.trace ((Rᴴ * X) * (Rᴴ * X)ᴴ) =
        Matrix.trace ((R * Rᴴ) * (X * Xᴴ)) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      Matrix.trace ((Rᴴ * X) * (Xᴴ * R)) =
          Matrix.trace (Rᴴ * (X * Xᴴ * R)) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace ((X * Xᴴ * R) * Rᴴ) :=
        Matrix.trace_mul_comm Rᴴ (X * Xᴴ * R)
      _ = Matrix.trace ((R * Rᴴ) * (X * Xᴴ)) := by
        calc
          Matrix.trace ((X * Xᴴ * R) * Rᴴ) =
              Matrix.trace ((X * Xᴴ) * (R * Rᴴ)) := by
                congr 1
                noncomm_ring
          _ = Matrix.trace ((R * Rᴴ) * (X * Xᴴ)) := by
            exact Matrix.trace_mul_comm (X * Xᴴ) (R * Rᴴ)
  have hQtrace :
      Matrix.trace ((Q * X) * (Q * X)ᴴ) =
        Matrix.trace ((Q * Q) * (X * Xᴴ)) := by
    rw [Matrix.conjTranspose_mul, hQstar]
    calc
      Matrix.trace ((Q * X) * (Xᴴ * Q)) =
          Matrix.trace ((Q * X * Xᴴ) * Q) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace (Q * (Q * X * Xᴴ)) :=
        Matrix.trace_mul_comm (Q * X * Xᴴ) Q
      _ = Matrix.trace ((Q * Q) * (X * Xᴴ)) := by
        congr 1
        noncomm_ring
  have hcycle :
      Matrix.trace (Xᴴ * (Q - Q * Q) * X) =
        Matrix.trace (X * Xᴴ) -
          Matrix.trace ((Rᴴ * X) * (Rᴴ * X)ᴴ) -
            Matrix.trace ((Q * X) * (Q * X)ᴴ) := by
    have hleft :
        Matrix.trace (Xᴴ * (Q - Q * Q) * X) =
          Matrix.trace ((Q - Q * Q) * (X * Xᴴ)) := by
      calc
        Matrix.trace (Xᴴ * (Q - Q * Q) * X) =
            Matrix.trace (((Q - Q * Q) * X) * Xᴴ) := by
              calc
                Matrix.trace (Xᴴ * (Q - Q * Q) * X) =
                    Matrix.trace (Xᴴ * ((Q - Q * Q) * X)) := by
                      congr 1
                      noncomm_ring
                _ = Matrix.trace (((Q - Q * Q) * X) * Xᴴ) :=
                  Matrix.trace_mul_comm Xᴴ ((Q - Q * Q) * X)
        _ = Matrix.trace ((Q - Q * Q) * (X * Xᴴ)) := by
          congr 1
          noncomm_ring
    rw [hleft, hRtrace, hQtrace]
    dsimp [Q]
    simp only [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul]
  have hcard : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hnormNonneg :
      0 ≤ (normTrace Y (Xᴴ * (Q - Q * Q) * X)).re := by
    unfold normTrace
    simpa using div_nonneg htraceNonneg hcard.le
  have hnormIdentity :
      normTrace Y (Xᴴ * (Q - Q * Q) * X) =
        (hsNormSq Y X : ℂ) - (hsNormSq Y (Rᴴ * X) : ℂ) -
          (hsNormSq Y (Q * X) : ℂ) := by
    calc
      normTrace Y (Xᴴ * (Q - Q * Q) * X) =
          normTrace Y (X * Xᴴ) -
            normTrace Y ((Rᴴ * X) * (Rᴴ * X)ᴴ) -
              normTrace Y ((Q * X) * (Q * X)ᴴ) := by
        unfold normTrace
        rw [hcycle]
        ring
      _ = (hsNormSq Y X : ℂ) - (hsNormSq Y (Rᴴ * X) : ℂ) -
          (hsNormSq Y (Q * X) : ℂ) := by
        rw [← ofReal_hsNormSq Y X, ← ofReal_hsNormSq Y (Rᴴ * X),
          ← ofReal_hsNormSq Y (Q * X)]
  rw [hnormIdentity] at hnormNonneg
  norm_num at hnormNonneg
  dsimp [Q] at hnormNonneg ⊢
  linarith

/-- The trace expansion behind the contraction product inequality. -/
theorem normTrace_gram_deficiency_product (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (A B : Matrix Y Y ℂ) :
    normTrace Y ((1 - Aᴴ * A) * (1 - B * Bᴴ)) =
      (1 : ℂ) - (hsNormSq Y A : ℂ) - (hsNormSq Y B : ℂ) +
        (hsNormSq Y (A * B) : ℂ) := by
  have hc : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hY.ne'
  have hexpand :
      (1 - Aᴴ * A) * (1 - B * Bᴴ) =
        1 - B * Bᴴ - Aᴴ * A + (Aᴴ * A) * (B * Bᴴ) := by
    noncomm_ring
  unfold normTrace
  rw [hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_one, Matrix.trace_mul_comm Aᴴ A,
    ← ofReal_sum_normSq Y A, ← ofReal_sum_normSq Y B]
  have hAB :
      Matrix.trace ((Aᴴ * A) * (B * Bᴴ)) =
        Matrix.trace ((A * B) * (A * B)ᴴ) := by
    rw [Matrix.conjTranspose_mul]
    calc
      Matrix.trace ((Aᴴ * A) * (B * Bᴴ)) =
          Matrix.trace (Aᴴ * (A * (B * Bᴴ))) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace ((A * (B * Bᴴ)) * Aᴴ) :=
        Matrix.trace_mul_comm Aᴴ (A * (B * Bᴴ))
      _ = Matrix.trace ((A * B) * (Bᴴ * Aᴴ)) := by
            simp [Matrix.mul_assoc]
  rw [hAB, ← ofReal_sum_normSq Y (A * B)]
  unfold hsNormSq
  push_cast
  field_simp
  ring

/-- Two contractions cannot lose more normalized Hilbert--Schmidt mass in a
product than the sum of their two individual deficiencies. -/
theorem one_sub_hsNormSq_mul_le_add_deficiencies
    (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (A B : Matrix Y Y ℂ) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    1 - hsNormSq Y (A * B) ≤
      (1 - hsNormSq Y A) + (1 - hsNormSq Y B) := by
  have hD := one_sub_conjTranspose_mul_posSemidef_of_l2_opNorm_le_one Y A hA
  have hBstar : ‖Bᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hB
  have hE := one_sub_conjTranspose_mul_posSemidef_of_l2_opNorm_le_one Y Bᴴ hBstar
  rw [Matrix.conjTranspose_conjTranspose] at hE
  have hnonneg := re_normTrace_mul_nonneg_of_posSemidef Y hY hD hE
  rw [normTrace_gram_deficiency_product Y hY A B] at hnonneg
  norm_num at hnonneg ⊢
  linarith

/-- **Multiplicative-only Leavitt obstruction.**  If four contractions have
the two right-inverse defects and one cross-product defect at most `ε`, then
`ε ≥ 2 - sqrt 3`.  The weaker rational consequence `ε ≥ 1/4` is exposed
below as the convenient theorem used by the atlas endpoint. -/
theorem two_sub_sqrt_three_le_of_leavitt_product_defects
    (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (T₀ S₀ T₁ S₁ : Matrix Y Y ℂ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hT₀ : ‖T₀‖ ≤ 1) (hS₀ : ‖S₀‖ ≤ 1)
    (hT₁ : ‖T₁‖ ≤ 1) (hS₁ : ‖S₁‖ ≤ 1)
    (h00 : hsNorm Y (T₀ * S₀ - 1) ≤ ε)
    (h11 : hsNorm Y (T₁ * S₁ - 1) ≤ ε)
    (h01 : hsNorm Y (T₀ * S₁) ≤ ε) :
    2 - Real.sqrt 3 ≤ ε := by
  have factor_sq_lower (T S : Matrix Y Y ℂ) (hT : ‖T‖ ≤ 1)
      (hdef : hsNorm Y (T * S - 1) ≤ ε) :
      (1 - ε) ^ 2 ≤ hsNormSq Y S := by
    have htrdef : ‖normTrace Y (T * S - 1)‖ ≤ ε :=
      (norm_normTrace_le_hsNorm Y _).trans hdef
    have htr : 1 - ε ≤ ‖normTrace Y (T * S)‖ := by
      have hone : ‖(1 : ℂ)‖ ≤
          ‖normTrace Y (T * S)‖ + ‖normTrace Y (T * S) - 1‖ := by
        calc
          ‖(1 : ℂ)‖ = ‖normTrace Y (T * S) +
              (1 - normTrace Y (T * S))‖ := by ring_nf
          _ ≤ ‖normTrace Y (T * S)‖ +
              ‖1 - normTrace Y (T * S)‖ := norm_add_le _ _
          _ = ‖normTrace Y (T * S)‖ +
              ‖normTrace Y (T * S) - 1‖ := by rw [norm_sub_rev]
      rw [normTrace_sub, normTrace_one' Y hY] at htrdef
      norm_num at hone
      linarith
    have htraceSq : (1 - ε) ^ 2 ≤ hsNormSq Y (T * S) := by
      have hnonneg : 0 ≤ 1 - ε := sub_nonneg.mpr hε1
      have hsquare : (1 - ε) ^ 2 ≤ ‖normTrace Y (T * S)‖ ^ 2 :=
        (sq_le_sq₀ hnonneg (norm_nonneg _)).mpr htr
      exact hsquare.trans (by
        simpa [Complex.sq_norm] using normSq_normTrace_le_hsNormSq Y (T * S))
    have hmul := hsNormSq_mul_le_sq_l2_opNorm_mul Y T S
    have hTsq : ‖T‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg T]
    have hSnonneg := hsNormSq_nonneg Y S
    calc
      (1 - ε) ^ 2 ≤ hsNormSq Y (T * S) := htraceSq
      _ ≤ ‖T‖ ^ 2 * hsNormSq Y S := hmul
      _ ≤ hsNormSq Y S := by nlinarith
  have hT₀sq : (1 - ε) ^ 2 ≤ hsNormSq Y T₀ :=
    by
      have hS₀star : ‖S₀ᴴ‖ ≤ 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact hS₀
      have hstar : hsNorm Y (S₀ᴴ * T₀ᴴ - 1) ≤ ε := by
        have hct : (T₀ * S₀ - 1)ᴴ = S₀ᴴ * T₀ᴴ - 1 := by simp
        unfold hsNorm at h00 ⊢
        rw [← hct, hsNormSq_conjTranspose]
        exact h00
      have h := factor_sq_lower S₀ᴴ T₀ᴴ hS₀star hstar
      rwa [hsNormSq_conjTranspose] at h
  have hS₁sq : (1 - ε) ^ 2 ≤ hsNormSq Y S₁ :=
    factor_sq_lower T₁ S₁ hT₁ h11
  have hproduct :=
    one_sub_hsNormSq_mul_le_add_deficiencies
      Y hY T₀ S₁ hT₀ hS₁
  have hcross : hsNormSq Y (T₀ * S₁) ≤ ε ^ 2 := by
    unfold hsNorm at h01
    have hsnonneg := hsNormSq_nonneg Y (T₀ * S₁)
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hε0).mpr h01
    rwa [Real.sq_sqrt hsnonneg] at hsquare
  have hquad : 1 - 4 * ε + ε ^ 2 ≤ 0 := by
    nlinarith [hT₀sq, hS₁sq, hproduct, hcross]
  have hsqrt3nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  by_contra h
  have hlt : ε < 2 - Real.sqrt 3 := lt_of_not_ge h
  nlinarith

/-- Rational form of the multiplicative-only obstruction. -/
theorem one_fourth_le_of_leavitt_product_defects
    (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (T₀ S₀ T₁ S₁ : Matrix Y Y ℂ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hT₀ : ‖T₀‖ ≤ 1) (hS₀ : ‖S₀‖ ≤ 1)
    (hT₁ : ‖T₁‖ ≤ 1) (hS₁ : ‖S₁‖ ≤ 1)
    (h00 : hsNorm Y (T₀ * S₀ - 1) ≤ ε)
    (h11 : hsNorm Y (T₁ * S₁ - 1) ≤ ε)
    (h01 : hsNorm Y (T₀ * S₁) ≤ ε) :
    (1 / 4 : ℝ) ≤ ε := by
  have hmain := two_sub_sqrt_three_le_of_leavitt_product_defects
    Y hY T₀ S₀ T₁ S₁ ε hε0 hε1 hT₀ hS₀ hT₁ hS₁ h00 h11 h01
  have hsqrt3lt : Real.sqrt 3 < 7 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- Max-defect form of the sharp multiplicative-only contraction gap. -/
theorem two_sub_sqrt_three_le_max_leavitt_product_hsNorm
    (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (T₀ S₀ T₁ S₁ : Matrix Y Y ℂ)
    (hT₀ : ‖T₀‖ ≤ 1) (hS₀ : ‖S₀‖ ≤ 1)
    (hT₁ : ‖T₁‖ ≤ 1) (hS₁ : ‖S₁‖ ≤ 1) :
    2 - Real.sqrt 3 ≤
      max (hsNorm Y (T₀ * S₀ - 1))
        (max (hsNorm Y (T₁ * S₁ - 1)) (hsNorm Y (T₀ * S₁))) := by
  let ε := max (hsNorm Y (T₀ * S₀ - 1))
    (max (hsNorm Y (T₁ * S₁ - 1)) (hsNorm Y (T₀ * S₁)))
  have hε0 : 0 ≤ ε :=
    (hsNorm_nonneg Y (T₀ * S₀ - 1)).trans (le_max_left _ _)
  by_cases hε1 : ε ≤ 1
  · have h00 : hsNorm Y (T₀ * S₀ - 1) ≤ ε := le_max_left _ _
    have h11 : hsNorm Y (T₁ * S₁ - 1) ≤ ε :=
      (le_max_left _ _).trans (le_max_right _ _)
    have h01 : hsNorm Y (T₀ * S₁) ≤ ε :=
      (le_max_right _ _).trans (le_max_right _ _)
    exact two_sub_sqrt_three_le_of_leavitt_product_defects
      Y hY T₀ S₀ T₁ S₁ ε hε0 hε1 hT₀ hS₀ hT₁ hS₁ h00 h11 h01
  · have hεgt : 1 < ε := lt_of_not_ge hε1
    have hsqrt3nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hsqrt3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    change 2 - Real.sqrt 3 ≤ ε
    nlinarith

/-- **Unitary-pairing form of the multiplicative obstruction.**  Suppose
`U : W → V` is the unitary matrix of a flat finite pairing, while `Rᵢ` and
`Lⱼ` are contraction arrows on its two sides.  The diagonal pairing
identities and one cross identity cannot all have small normalized
Hilbert--Schmidt defect.

Right multiplication by `Uᴴ` turns the three displayed pairing defects into
the product defects for `Tᵢ = Rᵢᴴ` and `Sⱼ = U Lⱼ Uᴴ`.  This is the exact
finite-dimensional endpoint needed by the robust radical-quotient gate. -/
theorem two_sub_sqrt_three_le_max_unitary_pairing_defects
    (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (U R₀ L₀ R₁ L₁ : Matrix Y Y ℂ)
    (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hR₀ : ‖R₀‖ ≤ 1) (hL₀ : ‖L₀‖ ≤ 1)
    (hR₁ : ‖R₁‖ ≤ 1) (hL₁ : ‖L₁‖ ≤ 1) :
    2 - Real.sqrt 3 ≤
      max (hsNorm Y (R₀ᴴ * U * L₀ - U))
        (max (hsNorm Y (R₁ᴴ * U * L₁ - U))
          (hsNorm Y (R₀ᴴ * U * L₁))) := by
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hU
  have hUUstar : U * Uᴴ = 1 := by
    have h := hU
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hR₀star : ‖R₀ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hR₀
  have hR₁star : ‖R₁ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hR₁
  have hUL₀Ustar : ‖U * L₀ * Uᴴ‖ ≤ 1 := by
    rw [CStarRing.norm_mul_mem_unitary _ hUstar,
      CStarRing.norm_mem_unitary_mul _ hU]
    exact hL₀
  have hUL₁Ustar : ‖U * L₁ * Uᴴ‖ ≤ 1 := by
    rw [CStarRing.norm_mul_mem_unitary _ hUstar,
      CStarRing.norm_mem_unitary_mul _ hU]
    exact hL₁
  have hdef00 :
      hsNorm Y (R₀ᴴ * (U * L₀ * Uᴴ) - 1) =
        hsNorm Y (R₀ᴴ * U * L₀ - U) := by
    have hfactor :
        R₀ᴴ * (U * L₀ * Uᴴ) - 1 = (R₀ᴴ * U * L₀ - U) * Uᴴ := by
      rw [Matrix.sub_mul, hUUstar]
      noncomm_ring
    unfold hsNorm
    rw [hfactor, hsNormSq_mul_right Y hUstar]
  have hdef11 :
      hsNorm Y (R₁ᴴ * (U * L₁ * Uᴴ) - 1) =
        hsNorm Y (R₁ᴴ * U * L₁ - U) := by
    have hfactor :
        R₁ᴴ * (U * L₁ * Uᴴ) - 1 = (R₁ᴴ * U * L₁ - U) * Uᴴ := by
      rw [Matrix.sub_mul, hUUstar]
      noncomm_ring
    unfold hsNorm
    rw [hfactor, hsNormSq_mul_right Y hUstar]
  have hdef01 :
      hsNorm Y (R₀ᴴ * (U * L₁ * Uᴴ)) =
        hsNorm Y (R₀ᴴ * U * L₁) := by
    have hfactor :
        R₀ᴴ * (U * L₁ * Uᴴ) = (R₀ᴴ * U * L₁) * Uᴴ := by
      noncomm_ring
    unfold hsNorm
    rw [hfactor, hsNormSq_mul_right Y hUstar]
  have hgap := two_sub_sqrt_three_le_max_leavitt_product_hsNorm
    Y hY R₀ᴴ (U * L₀ * Uᴴ) R₁ᴴ (U * L₁ * Uᴴ)
    hR₀star hUL₀Ustar hR₁star hUL₁Ustar
  rwa [hdef00, hdef11, hdef01] at hgap

/-! ## Why a positive-rank carrier is not enough

The full-space hypotheses above are essential.  On a proper carrier, exact
right-inverse and cross-product relations can coexist: one forward arrow may
leave the carrier and its matching backward arrow may return it.  The
following `2 x 2` packet is the smallest exact counterexample.
-/

/-- The rank-one carrier used by the compressed-product counterexample. -/
def weightedLeavittCarrier : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, 0]

/-- A partial isometry taking the carrier line to its orthogonal line. -/
def weightedLeavittForward : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 0; 1, 0]

/-- The reverse partial isometry returning the orthogonal line to the
carrier. -/
def weightedLeavittBackward : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 0, 0]

/-- A proper carrier can satisfy the two diagonal compressed products and
one crossed compressed product exactly.  Here the zeroth forward and
backward arrows are both the carrier projection itself, while the first
arrows are `weightedLeavittForward` and `weightedLeavittBackward`.

Thus a trace floor for the carrier alone cannot replace an invariance (or
common reducing-sector) theorem for the arrows. -/
theorem properCarrier_exact_weighted_leavitt_relations :
    weightedLeavittCarrier * weightedLeavittCarrier * weightedLeavittCarrier =
        weightedLeavittCarrier ∧
      weightedLeavittBackward * weightedLeavittForward *
          weightedLeavittCarrier = weightedLeavittCarrier ∧
      weightedLeavittCarrier * weightedLeavittForward *
          weightedLeavittCarrier = 0 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [weightedLeavittCarrier, Matrix.mul_apply, Fin.sum_univ_succ]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [weightedLeavittCarrier, weightedLeavittForward,
        weightedLeavittBackward, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [weightedLeavittCarrier, weightedLeavittForward,
        Matrix.mul_apply, Fin.sum_univ_succ]

/-- The counterexample carrier is visibly nonzero and proper: its two
diagonal entries are `1` and `0`. -/
theorem weightedLeavittCarrier_diagonal :
    weightedLeavittCarrier 0 0 = 1 ∧ weightedLeavittCarrier 1 1 = 0 := by
  norm_num [weightedLeavittCarrier]

end GroupApproximation
