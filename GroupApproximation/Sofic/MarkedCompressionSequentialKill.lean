import GroupApproximation.Sofic.KazhdanCompressorCorner
import GroupApproximation.Sofic.MarkedCompressionVectorChain
import GroupApproximation.Sofic.NegativeCornerModel
import GroupApproximation.Sofic.NormUltraproductSequentialExtraction

/-!
# The sequential marked-compression kill theorem

Steps 11–12 of the marked-compression argument.  Given inclusion data `D` in
a group `E` and an operator-norm almost representation `B` of `E` on which
the marked word tends to `-1` (the negative-corner input produced by the
involution-rounding layer), the Kazhdan-compressor control of the previous
file forces a contradiction:

* the lamp microstate `Vₜ V_c Vₜᴴ`, viewed as a Hilbert–Schmidt vector, is
  asymptotically fixed by the adjoint `Γ`-action, hence by `ι a`, so the
  marked commutator microstate tends to `1` in normalized Hilbert–Schmidt
  distance;
* but the same microstate tracks `B.map n D.word → -1` in operator norm,
  hence in normalized Hilbert–Schmidt distance;
* the distance between `1` and `-1` is `2`, ruling both out at once.

Consequently a countable group carrying inclusion data with a nontrivial
marked word is not weak/operator-norm MF, modulo the negative-corner input,
which is quarantined in one explicitly stated stub at the end of the file.
-/

namespace GroupApproximation
namespace KazhdanCompressorCorner

open Matrix KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

universe u

/-! ## Pointwise quadratic estimates -/

theorem normSq_add_le (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]

theorem sum_normSq_add_le {Y : Type*} [Fintype Y] (x y : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((x + y) i) ≤
      2 * ∑ i : Y, Complex.normSq (x i) +
        2 * ∑ i : Y, Complex.normSq (y i) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ normSq_add_le (x i) (y i)

theorem sum_normSq_matrix_add_le {Y : Type*} [Fintype Y]
    (A C : Matrix Y Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq (A i j + C i j) ≤
      2 * ∑ i : Y, ∑ j : Y, Complex.normSq (A i j) +
        2 * ∑ i : Y, ∑ j : Y, Complex.normSq (C i j) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ ↦ normSq_add_le (A i j) (C i j)

theorem sum_normSq_matrix_neg {Y : Type*} [Fintype Y] (A : Matrix Y Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq (-A i j) =
      ∑ i : Y, ∑ j : Y, Complex.normSq (A i j) := by
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Complex.normSq_neg]

/-- Arithmetic–geometric mean bound for the real part of a pairing; the
elementary replacement for the Cauchy–Schwarz inequality. -/
theorem re_star_dotProduct_le {Y : Type*} [Fintype Y]
    {δ : ℝ} (hδ : 0 < δ) (a b : Y → ℂ) :
    (star a ⬝ᵥ b).re ≤
      (2 : ℝ)⁻¹ * (δ * ∑ i : Y, Complex.normSq (a i) +
        δ⁻¹ * ∑ i : Y, Complex.normSq (b i)) := by
  have hpt : ∀ i : Y, ((star a) i * b i).re ≤
      (2 : ℝ)⁻¹ * (δ * Complex.normSq (a i) +
        δ⁻¹ * Complex.normSq (b i)) := by
    intro i
    have hre : ((star a) i * b i).re =
        (a i).re * (b i).re + (a i).im * (b i).im := by
      simp only [Pi.star_apply, Complex.star_def, Complex.mul_re,
        Complex.conj_re, Complex.conj_im]
      ring
    have hδ' : 0 < δ⁻¹ := by positivity
    rw [hre, Complex.normSq_apply, Complex.normSq_apply]
    have e1 : (a i).re * (b i).re ≤
        (2 : ℝ)⁻¹ * (δ * ((a i).re * (a i).re) +
          δ⁻¹ * ((b i).re * (b i).re)) := by
      have hkey : 0 ≤ δ⁻¹ * (δ * (a i).re - (b i).re) ^ 2 :=
        mul_nonneg hδ'.le (sq_nonneg _)
      have hexp : δ⁻¹ * (δ * (a i).re - (b i).re) ^ 2 =
          δ * ((a i).re * (a i).re) - 2 * ((a i).re * (b i).re) +
            δ⁻¹ * ((b i).re * (b i).re) := by
        field_simp
        ring
      nlinarith [hkey, hexp]
    have e2 : (a i).im * (b i).im ≤
        (2 : ℝ)⁻¹ * (δ * ((a i).im * (a i).im) +
          δ⁻¹ * ((b i).im * (b i).im)) := by
      have hkey : 0 ≤ δ⁻¹ * (δ * (a i).im - (b i).im) ^ 2 :=
        mul_nonneg hδ'.le (sq_nonneg _)
      have hexp : δ⁻¹ * (δ * (a i).im - (b i).im) ^ 2 =
          δ * ((a i).im * (a i).im) - 2 * ((a i).im * (b i).im) +
            δ⁻¹ * ((b i).im * (b i).im) := by
        field_simp
        ring
      nlinarith [hkey, hexp]
    nlinarith [e1, e2]
  calc
    (star a ⬝ᵥ b).re = ∑ i : Y, ((star a) i * b i).re := by
      rw [dotProduct, Complex.re_sum]
    _ ≤ ∑ i : Y, (2 : ℝ)⁻¹ *
        (δ * Complex.normSq (a i) + δ⁻¹ * Complex.normSq (b i)) :=
      Finset.sum_le_sum fun i _ ↦ hpt i
    _ = (2 : ℝ)⁻¹ * (δ * ∑ i : Y, Complex.normSq (a i) +
        δ⁻¹ * ∑ i : Y, Complex.normSq (b i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1
      funext i
      ring

/-! ## Frobenius mass bookkeeping -/

/-- Division of both sides of an inequality by a positive constant. -/
theorem div_le_div_of_le_pos {a b c : ℝ} (hc : 0 < c) (h : a ≤ b) :
    a / c ≤ b / c := by
  rw [div_le_div_iff₀ hc hc]
  nlinarith

/-- Entrywise mass is dominated by dimension times squared operator norm. -/
theorem sum_normSq_le_card_mul_sq (Y : FiniteModel) (M : Matrix Y Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq (M i j) ≤
      Fintype.card Y * ‖M‖ ^ 2 := by
  have h := hsDistSq_le_sq_l2_opNorm Y M 0
  rw [hsDistSq, sub_zero] at h
  by_cases hzero : Fintype.card Y = 0
  · haveI hempty : IsEmpty Y := Fintype.card_eq_zero_iff.mp hzero
    simp
  · have hpos : (0 : ℝ) < Fintype.card Y := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_iff₀ hpos] at h
    have hsimp : ∀ i j : Y, M i j - (0 : Matrix Y Y ℂ) i j = M i j := by
      intro i j
      simp
    calc
      ∑ i : Y, ∑ j : Y, Complex.normSq (M i j) =
          ∑ i : Y, ∑ j : Y,
            Complex.normSq (M i j - (0 : Matrix Y Y ℂ) i j) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hsimp i j]
      _ ≤ ‖M‖ ^ 2 * Fintype.card Y := h
      _ = Fintype.card Y * ‖M‖ ^ 2 := by ring

/-- A unitary matrix has Frobenius mass exactly the dimension. -/
theorem sum_normSq_of_mem_unitary (Y : FiniteModel) {u : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq (u i j) = Fintype.card Y := by
  classical
  have hcol : ∀ j : Y, ∑ i : Y, Complex.normSq (u i j) = 1 := by
    intro j
    have hgram : uᴴ * u = 1 := by
      have h := Matrix.mem_unitaryGroup_iff'.mp hu
      rwa [Matrix.star_eq_conjTranspose] at h
    have hmass := sum_normSq_mulVec_of_star_mul_self hgram
      (Pi.single j (1 : ℂ))
    have hsingle : ∑ i : Y,
        Complex.normSq ((Pi.single j (1 : ℂ) : Y → ℂ) i) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hsingle] at hmass
    calc
      ∑ i : Y, Complex.normSq (u i j) =
          ∑ i : Y, Complex.normSq ((u *ᵥ Pi.single j (1 : ℂ)) i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Matrix.mulVec_single_one]
        rfl
      _ = 1 := hmass
  calc
    ∑ i : Y, ∑ j : Y, Complex.normSq (u i j) =
        ∑ j : Y, ∑ i : Y, Complex.normSq (u i j) := Finset.sum_comm
    _ = ∑ _j : Y, (1 : ℝ) := Finset.sum_congr rfl fun j _ ↦ hcol j
    _ = Fintype.card Y := by simp

/-- Squared triangle comparison for the normalized Hilbert–Schmidt
distance. -/
theorem hsDistSq_le_two_add_two (Y : FiniteModel) (A C M : Matrix Y Y ℂ) :
    hsDistSq Y A C ≤ 2 * hsDistSq Y A M + 2 * hsDistSq Y M C := by
  have hnum : ∑ i : Y, ∑ j : Y, Complex.normSq (A i j - C i j) ≤
      2 * ∑ i : Y, ∑ j : Y, Complex.normSq (A i j - M i j) +
        2 * ∑ i : Y, ∑ j : Y, Complex.normSq (M i j - C i j) := by
    calc
      ∑ i : Y, ∑ j : Y, Complex.normSq (A i j - C i j) =
          ∑ i : Y, ∑ j : Y,
            Complex.normSq ((A i j - M i j) + (M i j - C i j)) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        congr 1
        ring
      _ ≤ 2 * ∑ i : Y, ∑ j : Y, Complex.normSq (A i j - M i j) +
          2 * ∑ i : Y, ∑ j : Y, Complex.normSq (M i j - C i j) :=
        sum_normSq_matrix_add_le _ _
  by_cases hzero : Fintype.card Y = 0
  · haveI hempty : IsEmpty Y := Fintype.card_eq_zero_iff.mp hzero
    simp [hsDistSq]
  · have hpos : (0 : ℝ) < Fintype.card Y := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [hsDistSq, hsDistSq, hsDistSq, mul_div_assoc, mul_div_assoc,
      ← add_div]
    exact div_le_div_of_le_pos hpos hnum

theorem hsDistSq_comm (Y : FiniteModel) (A C : Matrix Y Y ℂ) :
    hsDistSq Y A C = hsDistSq Y C A := by
  rw [hsDistSq, hsDistSq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show A i j - C i j = -(C i j - A i j) by ring, Complex.normSq_neg]

/-- The squared normalized Hilbert–Schmidt distance between `1` and `-1`. -/
theorem hsDistSq_one_neg_one (Y : FiniteModel) (hY : 0 < Fintype.card Y) :
    hsDistSq Y (1 : Matrix Y Y ℂ) (-1) = 4 := by
  classical
  rw [hsDistSq]
  have hsum : ∑ i : Y, ∑ j : Y,
      Complex.normSq ((1 : Matrix Y Y ℂ) i j - (-1 : Matrix Y Y ℂ) i j) =
      4 * Fintype.card Y := by
    calc
      ∑ i : Y, ∑ j : Y,
          Complex.normSq ((1 : Matrix Y Y ℂ) i j -
            (-1 : Matrix Y Y ℂ) i j) =
          ∑ i : Y, ∑ j : Y, (if i = j then (4 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Matrix.neg_apply, sub_neg_eq_add, Matrix.one_apply,
          Matrix.one_apply]
        by_cases hij : i = j
        · rw [if_pos hij, if_pos hij, if_pos hij]
          norm_num [Complex.normSq_apply]
        · rw [if_neg hij, if_neg hij, if_neg hij]
          norm_num
      _ = ∑ _i : Y, (4 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_ite_eq (Finset.univ : Finset Y) i fun _ ↦ (4 : ℝ)]
        simp
      _ = 4 * Fintype.card Y := by
        rw [Finset.sum_const]
        simp [mul_comm]
  rw [hsum]
  have hne : (Fintype.card Y : ℝ) ≠ 0 := by positivity
  field_simp

/-- Norm bound for unitary matrices over a possibly empty index type. -/
theorem norm_le_one_of_mem_unitary {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u : Matrix Y Y ℂ} (hu : u ∈ Matrix.unitaryGroup Y ℂ) : ‖u‖ ≤ 1 := by
  by_cases hY : Nonempty Y
  · exact le_of_eq (CStarRing.norm_of_mem_unitary hu)
  · haveI : IsEmpty Y := not_nonempty_iff.mp hY
    have hzero : u = 0 := Subsingleton.elim _ _
    rw [hzero]
    simp

/-- Commutator mass control: the deviation of a unitary commutator from `1`
is at most twice the deviation of the two unitaries, in normalized
Hilbert–Schmidt distance (squared: factor `4`). -/
theorem hsDistSq_commutator_one_le (Y : FiniteModel)
    {Dm Mm : Matrix Y Y ℂ} (hD : Dm ∈ Matrix.unitaryGroup Y ℂ)
    (hM : Mm ∈ Matrix.unitaryGroup Y ℂ) :
    hsDistSq Y (Dm * Mm * Dmᴴ * Mmᴴ) 1 ≤ 4 * hsDistSq Y Mm Dm := by
  classical
  have hDstar : Dm * Dmᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hD
    rwa [Matrix.star_eq_conjTranspose] at h
  have hMstar : Mm * Mmᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hM
    rwa [Matrix.star_eq_conjTranspose] at h
  have hfactor : Dm * Mm * Dmᴴ * Mmᴴ - 1 =
      (Dm * Mm - Mm * Dm) * (Dmᴴ * Mmᴴ) := by
    have hexp : (Dm * Mm - Mm * Dm) * (Dmᴴ * Mmᴴ) =
        Dm * Mm * Dmᴴ * Mmᴴ - Mm * (Dm * Dmᴴ) * Mmᴴ := by
      noncomm_ring
    rw [hexp, hDstar, Matrix.mul_one, hMstar]
  have hBnorm : ‖Dmᴴ * Mmᴴ‖ ≤ 1 := by
    calc
      ‖Dmᴴ * Mmᴴ‖ ≤ ‖Dmᴴ‖ * ‖Mmᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 := by
        refine mul_le_mul ?_ ?_ (norm_nonneg _) zero_le_one
        · rw [← Matrix.star_eq_conjTranspose, norm_star]
          exact norm_le_one_of_mem_unitary hD
        · rw [← Matrix.star_eq_conjTranspose, norm_star]
          exact norm_le_one_of_mem_unitary hM
      _ = 1 := one_mul _
  have hMnorm : ‖Mm‖ ≤ 1 := norm_le_one_of_mem_unitary hM
  -- mass estimates
  have hmass1 : ∑ i : Y, ∑ j : Y,
      Complex.normSq (((Dm * Mm - Mm * Dm) * (Dmᴴ * Mmᴴ)) i j) ≤
      ∑ i : Y, ∑ j : Y, Complex.normSq ((Dm * Mm - Mm * Dm) i j) := by
    calc
      ∑ i : Y, ∑ j : Y,
          Complex.normSq (((Dm * Mm - Mm * Dm) * (Dmᴴ * Mmᴴ)) i j) ≤
          ‖Dmᴴ * Mmᴴ‖ ^ 2 * ∑ i : Y, ∑ j : Y,
            Complex.normSq ((Dm * Mm - Mm * Dm) i j) :=
        sum_normSq_mul_right_le _ _
      _ ≤ 1 * ∑ i : Y, ∑ j : Y,
          Complex.normSq ((Dm * Mm - Mm * Dm) i j) := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · nlinarith [hBnorm, norm_nonneg (Dmᴴ * Mmᴴ)]
        · exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
            Complex.normSq_nonneg _
      _ = ∑ i : Y, ∑ j : Y,
          Complex.normSq ((Dm * Mm - Mm * Dm) i j) := one_mul _
  have hsplit : ∀ i j : Y, (Dm * Mm - Mm * Dm) i j =
      ((Dm - Mm) * Mm) i j + (Mm * (Mm - Dm)) i j := by
    intro i j
    have h : Dm * Mm - Mm * Dm = (Dm - Mm) * Mm + Mm * (Mm - Dm) := by
      noncomm_ring
    rw [h]
    rfl
  have hmass2 : ∑ i : Y, ∑ j : Y,
      Complex.normSq ((Dm * Mm - Mm * Dm) i j) ≤
      4 * ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm - Dm) i j) := by
    have hstep : ∑ i : Y, ∑ j : Y,
        Complex.normSq ((Dm * Mm - Mm * Dm) i j) ≤
        2 * ∑ i : Y, ∑ j : Y, Complex.normSq (((Dm - Mm) * Mm) i j) +
          2 * ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm * (Mm - Dm)) i j) := by
      calc
        ∑ i : Y, ∑ j : Y, Complex.normSq ((Dm * Mm - Mm * Dm) i j) =
            ∑ i : Y, ∑ j : Y, Complex.normSq
              (((Dm - Mm) * Mm) i j + (Mm * (Mm - Dm)) i j) := by
          refine Finset.sum_congr rfl fun i _ ↦
            Finset.sum_congr rfl fun j _ ↦ ?_
          rw [hsplit i j]
        _ ≤ _ := sum_normSq_matrix_add_le _ _
    have hnn : (0 : ℝ) ≤
        ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm - Dm) i j) :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
        Complex.normSq_nonneg _
    have hfirst : ∑ i : Y, ∑ j : Y,
        Complex.normSq (((Dm - Mm) * Mm) i j) ≤
        ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm - Dm) i j) := by
      calc
        ∑ i : Y, ∑ j : Y, Complex.normSq (((Dm - Mm) * Mm) i j) ≤
            ‖Mm‖ ^ 2 * ∑ i : Y, ∑ j : Y,
              Complex.normSq ((Dm - Mm) i j) :=
          sum_normSq_mul_right_le _ _
        _ ≤ 1 * ∑ i : Y, ∑ j : Y, Complex.normSq ((Dm - Mm) i j) := by
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · nlinarith [hMnorm, norm_nonneg Mm]
          · exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
              Complex.normSq_nonneg _
        _ = ∑ i : Y, ∑ j : Y, Complex.normSq ((Dm - Mm) i j) := one_mul _
        _ = ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm - Dm) i j) := by
          refine Finset.sum_congr rfl fun i _ ↦
            Finset.sum_congr rfl fun j _ ↦ ?_
          rw [show (Dm - Mm) i j = -((Mm - Dm) i j) by
            rw [Matrix.sub_apply, Matrix.sub_apply]; ring,
            Complex.normSq_neg]
    have hsecond : ∑ i : Y, ∑ j : Y,
        Complex.normSq ((Mm * (Mm - Dm)) i j) ≤
        ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm - Dm) i j) := by
      calc
        ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm * (Mm - Dm)) i j) ≤
            ‖Mm‖ ^ 2 * ∑ i : Y, ∑ j : Y,
              Complex.normSq ((Mm - Dm) i j) :=
          sum_normSq_mul_left_le _ _
        _ ≤ 1 * ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm - Dm) i j) := by
          refine mul_le_mul_of_nonneg_right ?_ hnn
          nlinarith [hMnorm, norm_nonneg Mm]
        _ = ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm - Dm) i j) := one_mul _
    linarith [hstep, hfirst, hsecond]
  -- assemble at the normalized level
  rw [hsDistSq, hsDistSq]
  by_cases hzero : Fintype.card Y = 0
  · haveI hempty : IsEmpty Y := Fintype.card_eq_zero_iff.mp hzero
    simp
  · have hpos : (0 : ℝ) < Fintype.card Y := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [mul_div_assoc]
    refine div_le_div_of_le_pos hpos ?_
    calc
      ∑ i : Y, ∑ j : Y,
          Complex.normSq ((Dm * Mm * Dmᴴ * Mmᴴ) i j -
            (1 : Matrix Y Y ℂ) i j) =
          ∑ i : Y, ∑ j : Y,
            Complex.normSq (((Dm * Mm - Mm * Dm) * (Dmᴴ * Mmᴴ)) i j) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        rw [show (Dm * Mm * Dmᴴ * Mmᴴ) i j - (1 : Matrix Y Y ℂ) i j =
            (Dm * Mm * Dmᴴ * Mmᴴ - 1) i j from rfl, hfactor]
      _ ≤ ∑ i : Y, ∑ j : Y,
          Complex.normSq ((Dm * Mm - Mm * Dm) i j) := hmass1
      _ ≤ 4 * ∑ i : Y, ∑ j : Y, Complex.normSq ((Mm - Dm) i j) := hmass2
      _ = 4 * ∑ i : Y, ∑ j : Y,
          Complex.normSq (Mm i j - Dm i j) := by
        refine congrArg (4 * ·) ?_
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Matrix.sub_apply]

/-! ## Vectorization linearity -/

@[simp] theorem matVec_sub {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A C : Matrix Y Y ℂ) : rowVec (A - C) = rowVec A - rowVec C := by
  funext p
  rfl

@[simp] theorem matVec_smul {Y : Type*} [Fintype Y] [DecidableEq Y]
    (c : ℂ) (A : Matrix Y Y ℂ) : rowVec (c • A) = c • rowVec A := by
  funext p
  rfl

@[simp] theorem matVec_add {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A C : Matrix Y Y ℂ) : rowVec (A + C) = rowVec A + rowVec C := by
  funext p
  rfl

theorem matVec_sum {Y : Type*} [Fintype Y] [DecidableEq Y]
    {I : Type*} (s : Finset I) (A : I → Matrix Y Y ℂ) :
    rowVec (∑ i ∈ s, A i) = ∑ i ∈ s, rowVec (A i) := by
  funext p
  simp [rowVec, Finset.sum_apply]

theorem sum_mulVec {Y : Type*} [Fintype Y] {I : Type*} (s : Finset I)
    (A : I → Matrix Y Y ℂ) (x : Y → ℂ) :
    (∑ i ∈ s, A i) *ᵥ x = ∑ i ∈ s, A i *ᵥ x := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-! ## Group-word microstate telescopes -/

variable {E : Type u} [Group E]

/-- Conjugate-transposition preserves operator-norm vanishing. -/
theorem OpNormVanishing.conjT {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : OpNormVanishing B x) :
    OpNormVanishing B (fun n ↦ (x n)ᴴ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [← Matrix.star_eq_conjTranspose, norm_star]
  exact hN n hn

/-- Conjugation microstates track conjugation exactly in the limit. -/
theorem conj_matrix_defect_vanishing (B : OpAlmostRepresentation E)
    (g x : E) :
    OpNormVanishing B (fun n ↦
      (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n x *
        (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        B.map n (g * x * g⁻¹)) := by
  have hb : ∀ (h : E) (n : ℕ),
      ‖(B.map n h : Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 :=
    fun h n ↦ norm_le_one_of_mem_unitary (B.map n h).2
  have hbstar : ∀ (h : E) (n : ℕ),
      ‖(B.map n h : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ ≤ 1 := by
    intro h n
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hb h n
  have q1 : OpNormVanishing B (fun n ↦
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n x -
        B.map n (g * x)) *
        (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ) :=
    ((multiplicativeDefect_vanishing B g x).neg.congr fun n ↦ by
      rw [neg_sub]).mul_right_of_norm_le_one _ (hbstar g)
  have q2 : OpNormVanishing B (fun n ↦
      (B.map n (g * x) : Matrix (B.model n) (B.model n) ℂ) *
        ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ -
          B.map n g⁻¹)) :=
    ((map_inv_vanishing B g).neg.congr fun n ↦ by
      rw [neg_sub]).mul_left_of_norm_le_one _ (hb (g * x))
  have q3 : OpNormVanishing B (fun n ↦
      (B.map n (g * x) : Matrix (B.model n) (B.model n) ℂ) *
        B.map n g⁻¹ - B.map n (g * x * g⁻¹)) :=
    (multiplicativeDefect_vanishing B (g * x) g⁻¹).neg.congr fun n ↦ by
      rw [neg_sub]
  refine ((q1.add q2).add q3).congr fun n ↦ ?_
  noncomm_ring

/-- The four-letter commutator word microstate telescopes to the microstate
of the commutator. -/
theorem word_product_defect_vanishing (B : OpAlmostRepresentation E)
    (x y : E) :
    OpNormVanishing B (fun n ↦
      (B.map n x : Matrix (B.model n) (B.model n) ℂ) * B.map n y *
        B.map n x⁻¹ * B.map n y⁻¹ -
        B.map n (x * y * x⁻¹ * y⁻¹)) := by
  have hb : ∀ (h : E) (n : ℕ),
      ‖(B.map n h : Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 :=
    fun h n ↦ norm_le_one_of_mem_unitary (B.map n h).2
  have hb2 : ∀ (h k : E) (n : ℕ),
      ‖(B.map n h : Matrix (B.model n) (B.model n) ℂ) * B.map n k‖ ≤ 1 :=
    fun h k n ↦ le_trans (Matrix.l2_opNorm_mul _ _)
      (mul_le_one₀ (hb h n) (norm_nonneg _) (hb k n))
  have p1 : OpNormVanishing B (fun n ↦
      ((B.map n x : Matrix (B.model n) (B.model n) ℂ) * B.map n y -
        B.map n (x * y)) * (B.map n x⁻¹ * B.map n y⁻¹)) :=
    ((multiplicativeDefect_vanishing B x y).neg.congr fun n ↦ by
      rw [neg_sub]).mul_right_of_norm_le_one _ (hb2 x⁻¹ y⁻¹)
  have p2 : OpNormVanishing B (fun n ↦
      ((B.map n (x * y) : Matrix (B.model n) (B.model n) ℂ) *
        B.map n x⁻¹ - B.map n (x * y * x⁻¹)) * B.map n y⁻¹) :=
    ((multiplicativeDefect_vanishing B (x * y) x⁻¹).neg.congr fun n ↦ by
      rw [neg_sub]).mul_right_of_norm_le_one _ (hb y⁻¹)
  have p3 : OpNormVanishing B (fun n ↦
      (B.map n (x * y * x⁻¹) : Matrix (B.model n) (B.model n) ℂ) *
        B.map n y⁻¹ - B.map n (x * y * x⁻¹ * y⁻¹)) :=
    (multiplicativeDefect_vanishing B (x * y * x⁻¹) y⁻¹).neg.congr
      fun n ↦ by rw [neg_sub]
  refine ((p1.add p2).add p3).congr fun n ↦ ?_
  noncomm_ring

/-! ## The lamp microstates -/

variable {Γ : Type} [Group Γ]

/-- The transported lamp microstate `Vₜ V_c Vₜᴴ`. -/
noncomputable def lampMatrix (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) (n : ℕ) :
    Matrix (B.model n) (B.model n) ℂ :=
  (B.map n D.t : Matrix (B.model n) (B.model n) ℂ) * B.map n D.c *
    (B.map n D.t : Matrix (B.model n) (B.model n) ℂ)ᴴ

/-- The `ι a`-conjugated lamp microstate. -/
noncomputable def conjLampMatrix (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) (n : ℕ) :
    Matrix (B.model n) (B.model n) ℂ :=
  (B.map n (D.iota D.a) : Matrix (B.model n) (B.model n) ℂ) *
    lampMatrix B D n *
    (B.map n (D.iota D.a) : Matrix (B.model n) (B.model n) ℂ)ᴴ

theorem lampMatrix_mem_unitaryGroup (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) (n : ℕ) :
    lampMatrix B D n ∈ Matrix.unitaryGroup (B.model n) ℂ :=
  mul_mem (mul_mem (B.map n D.t).2 (B.map n D.c).2)
    (conjTranspose_mem_unitaryGroup (B.map n D.t).2)

theorem conjLampMatrix_mem_unitaryGroup (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) (n : ℕ) :
    conjLampMatrix B D n ∈ Matrix.unitaryGroup (B.model n) ℂ :=
  mul_mem (mul_mem (B.map n (D.iota D.a)).2
    (lampMatrix_mem_unitaryGroup B D n))
    (conjTranspose_mem_unitaryGroup (B.map n (D.iota D.a)).2)

theorem lampMatrix_defect_vanishing (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) :
    OpNormVanishing B (fun n ↦
      lampMatrix B D n - B.map n (D.t * D.c * D.t⁻¹)) :=
  (conj_matrix_defect_vanishing B D.t D.c).congr fun n ↦ rfl

theorem conjLampMatrix_defect_vanishing (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) :
    OpNormVanishing B (fun n ↦
      conjLampMatrix B D n -
        B.map n (D.iota D.a * (D.t * D.c * D.t⁻¹) * (D.iota D.a)⁻¹)) := by
  have hb : ∀ (h : E) (n : ℕ),
      ‖(B.map n h : Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 :=
    fun h n ↦ norm_le_one_of_mem_unitary (B.map n h).2
  have hbstar : ∀ (h : E) (n : ℕ),
      ‖(B.map n h : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ ≤ 1 := by
    intro h n
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hb h n
  have h1 : OpNormVanishing B (fun n ↦
      (B.map n (D.iota D.a) : Matrix (B.model n) (B.model n) ℂ) *
        (lampMatrix B D n - B.map n (D.t * D.c * D.t⁻¹)) *
        (B.map n (D.iota D.a) : Matrix (B.model n) (B.model n) ℂ)ᴴ) :=
    ((lampMatrix_defect_vanishing B D).mul_left_of_norm_le_one _
      (hb (D.iota D.a))).mul_right_of_norm_le_one _ (hbstar (D.iota D.a))
  have h2 := conj_matrix_defect_vanishing B (D.iota D.a)
    (D.t * D.c * D.t⁻¹)
  refine (h1.add h2).congr fun n ↦ ?_
  rw [conjLampMatrix]
  noncomm_ring

/-- The commutator of the two lamp microstates. -/
noncomputable def commutatorMatrix (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) (n : ℕ) :
    Matrix (B.model n) (B.model n) ℂ :=
  lampMatrix B D n * conjLampMatrix B D n * (lampMatrix B D n)ᴴ *
    (conjLampMatrix B D n)ᴴ

theorem commutatorMatrix_defect_vanishing (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) :
    OpNormVanishing B (fun n ↦
      commutatorMatrix B D n -
        (B.map n D.word : Matrix (B.model n) (B.model n) ℂ)) := by
  have hb : ∀ (h : E) (n : ℕ),
      ‖(B.map n h : Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 :=
    fun h n ↦ norm_le_one_of_mem_unitary (B.map n h).2
  set x : E := D.t * D.c * D.t⁻¹ with hx
  set y : E := D.iota D.a * x * (D.iota D.a)⁻¹ with hy
  have hword : D.word = x * y * x⁻¹ * y⁻¹ := by
    rw [MarkedCompressionInclusionData.word, markedCompressionWord,
      commutatorElement_def]
  -- microstate approximations of the four letters
  have hA := lampMatrix_defect_vanishing B D
  have hB := conjLampMatrix_defect_vanishing B D
  have hAh : OpNormVanishing B (fun n ↦
      (lampMatrix B D n)ᴴ -
        (B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ)) := by
    have h1 := (lampMatrix_defect_vanishing B D).conjT
    have h2 := (map_inv_vanishing B x).neg
    refine (h1.add h2).congr fun n ↦ ?_
    rw [Matrix.conjTranspose_sub]
    abel
  have hBh : OpNormVanishing B (fun n ↦
      (conjLampMatrix B D n)ᴴ -
        (B.map n y⁻¹ : Matrix (B.model n) (B.model n) ℂ)) := by
    have h1 := (conjLampMatrix_defect_vanishing B D).conjT
    have h2 := (map_inv_vanishing B y).neg
    refine (h1.add h2).congr fun n ↦ ?_
    rw [Matrix.conjTranspose_sub]
    abel
  -- companion norm bounds
  have hlamp : ∀ n, ‖lampMatrix B D n‖ ≤ 1 :=
    fun n ↦ norm_le_one_of_mem_unitary (lampMatrix_mem_unitaryGroup B D n)
  have hconjlamp : ∀ n, ‖conjLampMatrix B D n‖ ≤ 1 :=
    fun n ↦ norm_le_one_of_mem_unitary
      (conjLampMatrix_mem_unitaryGroup B D n)
  have hlampstar : ∀ n, ‖(lampMatrix B D n)ᴴ‖ ≤ 1 := by
    intro n
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hlamp n
  have hconjlampstar : ∀ n, ‖(conjLampMatrix B D n)ᴴ‖ ≤ 1 := by
    intro n
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hconjlamp n
  have hmul2 : ∀ n, ‖conjLampMatrix B D n * (lampMatrix B D n)ᴴ *
      (conjLampMatrix B D n)ᴴ‖ ≤ 1 := by
    intro n
    calc
      ‖conjLampMatrix B D n * (lampMatrix B D n)ᴴ *
          (conjLampMatrix B D n)ᴴ‖ ≤
          ‖conjLampMatrix B D n * (lampMatrix B D n)ᴴ‖ *
            ‖(conjLampMatrix B D n)ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 := by
        refine mul_le_mul ?_ (hconjlampstar n) (norm_nonneg _) zero_le_one
        exact le_trans (Matrix.l2_opNorm_mul _ _)
          (mul_le_one₀ (hconjlamp n) (norm_nonneg _) (hlampstar n))
      _ = 1 := one_mul _
  have hmulVxy : ∀ n,
      ‖(B.map n x : Matrix (B.model n) (B.model n) ℂ) * B.map n y‖ ≤ 1 :=
    fun n ↦ le_trans (Matrix.l2_opNorm_mul _ _)
      (mul_le_one₀ (hb x n) (norm_nonneg _) (hb y n))
  have hmulVxyx : ∀ n,
      ‖(B.map n x : Matrix (B.model n) (B.model n) ℂ) * B.map n y *
        B.map n x⁻¹‖ ≤ 1 :=
    fun n ↦ le_trans (Matrix.l2_opNorm_mul _ _)
      (mul_le_one₀ (hmulVxy n) (norm_nonneg _) (hb x⁻¹ n))
  have hmullampstar2 : ∀ n, ‖(lampMatrix B D n)ᴴ *
      (conjLampMatrix B D n)ᴴ‖ ≤ 1 :=
    fun n ↦ le_trans (Matrix.l2_opNorm_mul _ _)
      (mul_le_one₀ (hlampstar n) (norm_nonneg _) (hconjlampstar n))
  -- the five telescoping brackets
  have t1 : OpNormVanishing B (fun n ↦
      (lampMatrix B D n -
        (B.map n x : Matrix (B.model n) (B.model n) ℂ)) *
        (conjLampMatrix B D n * (lampMatrix B D n)ᴴ *
          (conjLampMatrix B D n)ᴴ)) :=
    hA.mul_right_of_norm_le_one _ hmul2
  have t2 : OpNormVanishing B (fun n ↦
      (B.map n x : Matrix (B.model n) (B.model n) ℂ) *
        (conjLampMatrix B D n -
          (B.map n y : Matrix (B.model n) (B.model n) ℂ)) *
        ((lampMatrix B D n)ᴴ * (conjLampMatrix B D n)ᴴ)) :=
    (hB.mul_left_of_norm_le_one _ (hb x)).mul_right_of_norm_le_one _
      hmullampstar2
  have t3 : OpNormVanishing B (fun n ↦
      (B.map n x : Matrix (B.model n) (B.model n) ℂ) * B.map n y *
        ((lampMatrix B D n)ᴴ -
          (B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ)) *
        (conjLampMatrix B D n)ᴴ) := by
    have h := (hAh.mul_left_of_norm_le_one
      (fun n ↦ (B.map n x : Matrix (B.model n) (B.model n) ℂ) *
        B.map n y) hmulVxy).mul_right_of_norm_le_one _ hconjlampstar
    exact h.congr fun n ↦ by noncomm_ring
  have t4 : OpNormVanishing B (fun n ↦
      (B.map n x : Matrix (B.model n) (B.model n) ℂ) * B.map n y *
        B.map n x⁻¹ *
        ((conjLampMatrix B D n)ᴴ -
          (B.map n y⁻¹ : Matrix (B.model n) (B.model n) ℂ))) := by
    have h := hBh.mul_left_of_norm_le_one
      (fun n ↦ (B.map n x : Matrix (B.model n) (B.model n) ℂ) *
        B.map n y * B.map n x⁻¹) hmulVxyx
    exact h.congr fun n ↦ by noncomm_ring
  have t5 := word_product_defect_vanishing B x y
  refine ((((t1.add t2).add t3).add t4).add t5).congr fun n ↦ ?_
  rw [hword, commutatorMatrix]
  noncomm_ring

/-! ## Finite uniformization over the generating set -/

theorem eventually_forall_finset {I : Type*} (S : Finset I) (f : I → ℕ → ℝ)
    (h : ∀ s ∈ S, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, f s n ≤ ε)
    {ε : ℝ} (hε : 0 < ε) : ∃ N, ∀ n ≥ N, ∀ s ∈ S, f s n ≤ ε := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    exact ⟨0, fun n _ s hs ↦ absurd hs (Finset.not_mem_empty s)⟩
  · intro i s _ ih h
    obtain ⟨N₁, h₁⟩ := h i (Finset.mem_insert_self i s) ε hε
    obtain ⟨N₂, h₂⟩ := ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
    refine ⟨max N₁ N₂, fun n hn j hj ↦ ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h₁ n ((le_max_left _ _).trans hn)
    · exact h₂ n ((le_max_right _ _).trans hn) j hj

/-! ## The lamp Laplacian identity -/

/-- The Laplacian displacement of the flattened lamp microstate is the
flattening of an explicit averaged conjugation defect. -/
theorem lamp_laplacian_matVec (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) (S : Finset Γ) (hone : 1 ∈ S)
    (n : ℕ) :
    rowVec (B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
      hermitianAverage (gammaAdjoint B D) S n *ᵥ
        rowVec (B.map n D.c : Matrix (B.model n) (B.model n) ℂ) =
    rowVec ((2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
      (((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            B.map n D.c *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        ((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            B.map n D.c *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ))))) := by
  classical
  have hcardC : ((S.card : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, hone⟩
  set Vc : Matrix (B.model n) (B.model n) ℂ := B.map n D.c with hVc
  -- the adjoint microstates act on the flattened lamp by conjugation
  have hdict : ∀ s : Γ,
      ((gammaAdjoint B D).map n s :
        Matrix ((B.adjoint.model n) : Type)
          ((B.adjoint.model n) : Type) ℂ) *ᵥ rowVec Vc =
      rowVec ((B.map n (D.iota s) :
        Matrix (B.model n) (B.model n) ℂ) * Vc *
        (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
    intro s
    exact conjDouble_mulVec_rowVec _ _
  have hdictStar : ∀ s : Γ,
      ((gammaAdjoint B D).map n s :
        Matrix ((B.adjoint.model n) : Type)
          ((B.adjoint.model n) : Type) ℂ)ᴴ *ᵥ rowVec Vc =
      rowVec ((B.map n (D.iota s) :
        Matrix (B.model n) (B.model n) ℂ)ᴴ * Vc *
        (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)) := by
    intro s
    have h : ((gammaAdjoint B D).map n s :
        Matrix ((B.adjoint.model n) : Type)
          ((B.adjoint.model n) : Type) ℂ)ᴴ =
        conjDouble
          ((B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) :=
      (conjDouble_conjTranspose _).symm
    rw [h]
    have h2 := conjDouble_mulVec_rowVec
      ((B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) Vc
    rw [h2, Matrix.conjTranspose_conjTranspose]
  -- expand the Hermitian average applied to the flattened lamp
  have haverage : hermitianAverage (gammaAdjoint B D) S n *ᵥ rowVec Vc =
      (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
        (rowVec ((B.map n (D.iota s) :
            Matrix (B.model n) (B.model n) ℂ) * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          rowVec ((B.map n (D.iota s) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)))) := by
    rw [hermitianAverage, Matrix.add_mulVec, Matrix.smul_mulVec_assoc]
    have hM : matrixAverage (gammaAdjoint B D) S n *ᵥ rowVec Vc =
        (S.card : ℂ)⁻¹ • ∑ s ∈ S,
          rowVec ((B.map n (D.iota s) :
            Matrix (B.model n) (B.model n) ℂ) * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
      rw [matrixAverage, Matrix.smul_mulVec_assoc, sum_mulVec]
      congr 1
      exact Finset.sum_congr rfl fun s _ ↦ hdict s
    have hMstar : (matrixAverage (gammaAdjoint B D) S n)ᴴ *ᵥ rowVec Vc =
        (S.card : ℂ)⁻¹ • ∑ s ∈ S,
          rowVec ((B.map n (D.iota s) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)) := by
      have hexpand : (matrixAverage (gammaAdjoint B D) S n)ᴴ =
          (S.card : ℂ)⁻¹ • ∑ s ∈ S,
            ((gammaAdjoint B D).map n s :
              Matrix ((B.adjoint.model n) : Type)
                ((B.adjoint.model n) : Type) ℂ)ᴴ := by
        rw [matrixAverage, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_sum]
        congr 1
        rw [star_inv₀]
        norm_cast
      rw [hexpand, Matrix.smul_mulVec_assoc, sum_mulVec]
      congr 1
      exact Finset.sum_congr rfl fun s _ ↦ hdictStar s
    rw [hM, hMstar, ← smul_add, ← Finset.sum_add_distrib]
  rw [haverage]
  -- pull the flattening out and finish with a matrix identity
  have hlin : (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
      (rowVec ((B.map n (D.iota s) :
          Matrix (B.model n) (B.model n) ℂ) * Vc *
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        rowVec ((B.map n (D.iota s) :
          Matrix (B.model n) (B.model n) ℂ)ᴴ * Vc *
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)))) =
      rowVec ((2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ +
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)))) := by
    rw [matVec_smul, matVec_smul, matVec_sum]
    congr 2
    exact Finset.sum_congr rfl fun s _ ↦ (matVec_add _ _).symm
  rw [hlin, ← matVec_sub]
  congr 1
  -- the pure matrix rearrangement
  have honeM : Vc = (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ _s ∈ S,
      (Vc + Vc)) := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul,
      smul_smul]
    have : (2 : ℂ)⁻¹ * ((S.card : ℂ)⁻¹ * (S.card : ℂ)) • (Vc + Vc) =
        (2 : ℂ)⁻¹ • (Vc + Vc) := by
      rw [inv_mul_cancel₀ hcardC]
      norm_num
    rw [show (2 : ℂ)⁻¹ * ((S.card : ℂ)⁻¹ * (S.card : ℂ)) =
        (2 : ℂ)⁻¹ * (S.card : ℂ)⁻¹ * (S.card : ℂ) by ring] at this
    rw [this]
    match_scalars <;> field_simp
  calc
    Vc - (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ +
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ))) =
        (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S, (Vc + Vc)) -
          (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
            ((B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
                Vc *
                (B.map n (D.iota s) :
                  Matrix (B.model n) (B.model n) ℂ)ᴴ +
              (B.map n (D.iota s) :
                Matrix (B.model n) (B.model n) ℂ)ᴴ * Vc *
                (B.map n (D.iota s) :
                  Matrix (B.model n) (B.model n) ℂ))) := by
      rw [← honeM]
    _ = (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((Vc - (B.map n (D.iota s) :
            Matrix (B.model n) (B.model n) ℂ) * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          (Vc - (B.map n (D.iota s) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ * Vc *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)))) := by
      rw [← smul_sub, ← smul_sub, ← Finset.sum_sub_distrib]
      congr 2
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      abel

/-! ## Step 11: the marked commutator collapses in Hilbert–Schmidt distance -/

/-- **The vector chain.**  Under the Kazhdan-compressor control, the marked
commutator microstate converges to the identity in normalized
Hilbert–Schmidt distance. -/
theorem commutatorMatrix_hsDistSq_vanishing {κ : ℝ} {S : Finset Γ} {θ : ℝ}
    (B : OpAlmostRepresentation E) (D : MarkedCompressionInclusionData Γ E)
    (hQ : IsKazhdanPair.{0, 0} Γ S κ) (hone : 1 ∈ S) (hκ1 : κ ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hθ4 : 1 - κ ^ 2 / (4 * S.card) < θ) (hθ1 : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n) (commutatorMatrix B D n) 1 ≤ ε := by
  classical
  intro ε hε
  have hθpos : 0 < 1 - θ := by linarith
  -- ε-BUDGET COUPLING (exactly tight, zero slack): the final `linarith`
  -- consumes 8·(ε/24) + 64·(ε/192) + 64·(ε/192) = ε against the committed
  -- 8/64/64 constants of the vector-chain lemmas.  Changing any constant on
  -- either side silently breaks the closing inequality; adjust both
  -- together.
  set η : ℝ := (1 - θ) * ε / 192 with hηdef
  have hηpos : 0 < η := by positivity
  have he₂ : (0 : ℝ) < ε / 192 := by linarith
  have he₃ : (0 : ℝ) < ε / 24 := by linarith
  have hfix : ∀ s ∈ S, ∀ ε' : ℝ, 0 < ε' → ∃ N, ∀ n ≥ N,
      ‖(B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
        B.map n D.c *
        (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        B.map n D.c‖ ≤ ε' := by
    intro s _ ε' hε'
    have hconj : D.iota s * D.c * (D.iota s)⁻¹ = D.c := by
      have h := (D.comm_c s).eq
      calc
        D.iota s * D.c * (D.iota s)⁻¹ =
            (D.c * D.iota s) * (D.iota s)⁻¹ := by rw [h]
        _ = D.c := by group
    have h := conj_matrix_defect_vanishing B (D.iota s) D.c
    rw [hconj] at h
    exact h ε' hε'
  obtain ⟨N₁, hN₁⟩ := eventually_forall_finset S _ hfix hηpos
  obtain ⟨N₂, hN₂⟩ := one_sub_corner_mul_moved_vanishing B D θ hQ hone hκ1
    hsymm hgen hθ4 hθ1 (Real.sqrt (ε / 192)) (Real.sqrt_pos.mpr he₂)
  obtain ⟨N₃, hN₃⟩ := displacement_vanishing B D θ hQ hone hκ1 hsymm hgen
    hθ4 D.a (Real.sqrt (ε / 24)) (Real.sqrt_pos.mpr he₃)
  refine ⟨max N₁ (max N₂ N₃), fun n hn ↦ ?_⟩
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₃ : n ≥ N₃ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  -- stage-n abbreviations
  have hr : 0 < Fintype.card (B.model n) := B.modelNonempty n
  -- generator defect bounds, both directions
  have hterm : ∀ s ∈ S,
      ‖(B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          B.map n D.c *
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ ≤
        η := by
    intro s hs
    rw [norm_sub_rev]
    exact hN₁ n hn₁ s hs
  have htermStar : ∀ s ∈ S,
      ‖(B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          B.map n D.c *
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)‖ ≤
        η := by
    intro s hs
    have hmem := (B.map n (D.iota s)).2
    have hUUstar :
        (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 := by
      have h := Matrix.mem_unitaryGroup_iff.mp hmem
      rwa [Matrix.star_eq_conjTranspose] at h
    have hkey :
        (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
              B.map n D.c *
              (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)) *
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ =
        (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          B.map n D.c *
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
          B.map n D.c := by
      have hexp :
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            ((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (D.iota s) :
                Matrix (B.model n) (B.model n) ℂ)ᴴ *
                B.map n D.c *
                (B.map n (D.iota s) :
                  Matrix (B.model n) (B.model n) ℂ)) *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ =
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            B.map n D.c *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
          ((B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
            B.map n D.c *
            ((B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
              (B.map n (D.iota s) :
                Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
        noncomm_ring
      rw [hexp, hUUstar, Matrix.one_mul, Matrix.mul_one]
    calc
      ‖(B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            B.map n D.c *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)‖ =
          ‖(B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            ((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (D.iota s) :
                Matrix (B.model n) (B.model n) ℂ)ᴴ *
                B.map n D.c *
                (B.map n (D.iota s) :
                  Matrix (B.model n) (B.model n) ℂ)) *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ :=
        (norm_unitary_conjugate hmem).symm
      _ = ‖(B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            B.map n D.c *
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
            B.map n D.c‖ := by rw [hkey]
      _ ≤ η := hN₁ n hn₁ s hs
  -- the averaged defect matrix
  have hGnorm : ‖(2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
      (((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            B.map n D.c *
            (B.map n (D.iota s) :
              Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        ((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            B.map n D.c *
            (B.map n (D.iota s) :
              Matrix (B.model n) (B.model n) ℂ))))‖ ≤ η := by
    have hsumnorm : ‖∑ s ∈ S,
        (((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
              B.map n D.c *
              (B.map n (D.iota s) :
                Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          ((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
              B.map n D.c *
              (B.map n (D.iota s) :
                Matrix (B.model n) (B.model n) ℂ)))‖ ≤
        S.card * (2 * η) := by
      calc
        ‖∑ s ∈ S, _‖ ≤ ∑ s ∈ S,
            ‖(((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
                (B.map n (D.iota s) :
                  Matrix (B.model n) (B.model n) ℂ) *
                  B.map n D.c *
                  (B.map n (D.iota s) :
                    Matrix (B.model n) (B.model n) ℂ)ᴴ) +
              ((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
                (B.map n (D.iota s) :
                  Matrix (B.model n) (B.model n) ℂ)ᴴ *
                  B.map n D.c *
                  (B.map n (D.iota s) :
                    Matrix (B.model n) (B.model n) ℂ)))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _s ∈ S, (2 * η) := by
          refine Finset.sum_le_sum fun s hs ↦ ?_
          exact (norm_add_le _ _).trans (add_le_add (hterm s hs) (htermStar s hs))
        _ = S.card * (2 * η) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    rw [norm_smul, norm_smul]
    have hcardC : ‖(S.card : ℂ)⁻¹‖ = (S.card : ℝ)⁻¹ := by
      rw [norm_inv, norm_natCast]
    rw [hcardC]
    norm_num
    calc
      (S.card : ℝ)⁻¹ * ‖∑ s ∈ S,
          (((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
                B.map n D.c *
                (B.map n (D.iota s) :
                  Matrix (B.model n) (B.model n) ℂ)ᴴ) +
            ((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
                B.map n D.c *
                (B.map n (D.iota s) :
                  Matrix (B.model n) (B.model n) ℂ)))‖ / 2 ≤
          (S.card : ℝ)⁻¹ * (S.card * (2 * η)) / 2 := by
        gcongr
      _ = η := by
        field_simp
  -- Spectral capture of the root lamp vector.
  let H := hermitianAverage (gammaAdjoint B D) S n
  let P := cornerProjection B D S θ n
  let ξ := rowVec (B.map n D.c : Matrix (B.model n) (B.model n) ℂ)
  have hHherm : H.IsHermitian := by
    exact hermitianAverage_conjTranspose (gammaAdjoint B D) S n
  have hHnorm : ‖H‖ ≤ 1 := norm_hermitianAverage_le_one _ S hone n
  have hresidual :
      ∑ i : (B.adjoint.model n), Complex.normSq ((ξ - H *ᵥ ξ) i) ≤
        Fintype.card (B.model n) * η ^ 2 := by
    have hid := lamp_laplacian_matVec B D S hone n
    rw [show ξ - H *ᵥ ξ =
        rowVec ((2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
          (((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ) *
                B.map n D.c *
                (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
            ((B.map n D.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
                B.map n D.c *
                (B.map n (D.iota s) : Matrix (B.model n) (B.model n) ℂ))))) by
          exact hid]
    rw [sum_normSq_rowVec]
    exact (sum_normSq_le_card_mul_sq _ _).trans (by
      gcongr)
  have hxiMass : ∑ i : (B.adjoint.model n), Complex.normSq (ξ i) =
      Fintype.card (B.model n) := by
    rw [show ξ = rowVec (B.map n D.c : Matrix (B.model n) (B.model n) ℂ) by rfl,
      sum_normSq_rowVec]
    exact sum_normSq_of_mem_unitary _ (B.map n D.c).2
  have henergy : (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
      η * Fintype.card (B.model n) := by
    have hamgm := re_star_dotProduct_le hηpos ξ (ξ - H *ᵥ ξ)
    rw [hxiMass]
    calc
      (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
          (2 : ℝ)⁻¹ *
            (η * Fintype.card (B.model n) + η⁻¹ *
              ∑ i : (B.adjoint.model n),
                Complex.normSq ((ξ - H *ᵥ ξ) i)) := hamgm
      _ ≤ (2 : ℝ)⁻¹ *
            (η * Fintype.card (B.model n) + η⁻¹ *
              (Fintype.card (B.model n) * η ^ 2)) := by
        gcongr
      _ = η * Fintype.card (B.model n) := by
        field_simp
        ring
  have hcaptureRaw := capture_vec H hHherm θ 0 hθ1.le (by positivity)
    (by simpa using hHnorm) ξ
  have hbelow : spectralBelow H hHherm θ = 1 - P := by
    rfl
  rw [hbelow, zero_mul, add_zero] at hcaptureRaw
  have hcapture :
      MarkedCompressionVectorChain.vecMass ((1 - P) *ᵥ
        rowVec
          (B.map n D.c : Matrix (B.model n) (B.model n) ℂ)) ≤
        (ε / 192) * Fintype.card (B.model n) := by
    rw [MarkedCompressionVectorChain.vecMass]
    change ∑ i : (B.adjoint.model n),
      Complex.normSq (((1 - P) *ᵥ ξ) i) ≤ _
    have hscaled : (1 - θ) * ∑ i : (B.adjoint.model n),
        Complex.normSq (((1 - P) *ᵥ ξ) i) ≤
        η * Fintype.card (B.model n) := hcaptureRaw.trans henergy
    rw [hηdef] at hscaled
    nlinarith
  have hstage := MarkedCompressionVectorChain.marked_commutator_hsDistSq_le
    hr (B.map n (D.iota D.a)).2 (B.map n D.t).2 (B.map n D.c).2
    (cornerProjection_isOrthogonalProjection B D S θ n)
    (hN₃ n hn₃) (hN₂ n hn₂) hcapture
  have hsqrt₂ : (Real.sqrt (ε / 192)) ^ 2 = ε / 192 :=
    Real.sq_sqrt he₂.le
  have hsqrt₃ : (Real.sqrt (ε / 24)) ^ 2 = ε / 24 :=
    Real.sq_sqrt he₃.le
  have hstage' : hsDistSq (B.model n) (commutatorMatrix B D n) 1 ≤
      8 * (Real.sqrt (ε / 24)) ^ 2 +
        64 * (Real.sqrt (ε / 192)) ^ 2 + 64 * (ε / 192) := by
    simpa [lampMatrix, conjLampMatrix, commutatorMatrix, gammaAdjoint,
      OpAlmostRepresentation.adjoint_map, P] using hstage
  rw [hsqrt₂, hsqrt₃] at hstage'
  norm_num at hstage' ⊢
  linarith

/-! ## Step 12: the marked word cannot converge to the negative identity -/

/-- **Sequential marked-compression kill theorem.**

An operator-norm almost representation carrying the marked word to `-1`
cannot coexist with the Kazhdan compressor relations.  The conclusion is
purely sequential and makes no separation or faithfulness assumption. -/
theorem false_of_marked_word_tends_to_neg_one
    (B : OpAlmostRepresentation E) (D : MarkedCompressionInclusionData Γ E)
    (hnegative : OpNormVanishing B (fun n ↦
      (B.map n D.word : Matrix (B.model n) (B.model n) ℂ) + 1)) :
    False := by
  classical
  obtain ⟨S, κ, hone, hsymm, hgen, hκpos, hκone, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair
      D.kazhdan
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hgap : 0 < κ ^ 2 / (4 * (S.card : ℝ)) :=
    div_pos (sq_pos_of_pos hκpos) (mul_pos (by norm_num) hcard)
  let c₀ : ℝ := 1 - κ ^ 2 / (4 * S.card)
  let θ : ℝ := (c₀ + 1) / 2
  have hθ4 : 1 - κ ^ 2 / (4 * S.card) < θ := by
    dsimp [c₀, θ]
    linarith
  have hθ1 : θ < 1 := by
    dsimp [c₀, θ]
    linarith
  obtain ⟨N₁, hN₁⟩ := commutatorMatrix_hsDistSq_vanishing B D hpair hone
    hκone hsymm hgen hθ4 hθ1 (1 / 16) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := (commutatorMatrix_defect_vanishing B D)
    (1 / 4) (by norm_num)
  obtain ⟨N₃, hN₃⟩ := hnegative (1 / 4) (by norm_num)
  let n := max N₁ (max N₂ N₃)
  have hn₁ : n ≥ N₁ := le_max_left _ _
  have hn₂ : n ≥ N₂ :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hn₃ : n ≥ N₃ :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  let Y := B.model n
  let W : Matrix Y Y ℂ := B.map n D.word
  let M : Matrix Y Y ℂ := commutatorMatrix B D n
  have hY : 0 < Fintype.card Y := B.modelNonempty n
  have hcomm : hsDistSq Y M 1 ≤ 1 / 16 := hN₁ n hn₁
  have hdefNorm : ‖M - W‖ ≤ 1 / 4 := hN₂ n hn₂
  have hnegNorm : ‖W + 1‖ ≤ 1 / 4 := hN₃ n hn₃
  have hdef : hsDistSq Y M W ≤ 1 / 16 := by
    have h := hsDistSq_le_sq_l2_opNorm Y M W
    calc
      hsDistSq Y M W ≤ ‖M - W‖ ^ 2 := h
      _ ≤ (1 / 4 : ℝ) ^ 2 := by
        nlinarith [norm_nonneg (M - W)]
      _ = 1 / 16 := by norm_num
  have hneg : hsDistSq Y W (-1) ≤ 1 / 16 := by
    have h := hsDistSq_le_sq_l2_opNorm Y W (-1)
    rw [sub_neg_eq_add] at h
    calc
      hsDistSq Y W (-1) ≤ ‖W + 1‖ ^ 2 := h
      _ ≤ (1 / 4 : ℝ) ^ 2 := by
        nlinarith [norm_nonneg (W + 1)]
      _ = 1 / 16 := by norm_num
  have htriangle₁ := hsDistSq_le_two_add_two Y
    (1 : Matrix Y Y ℂ) (-1) M
  have htriangle₂ := hsDistSq_le_two_add_two Y M (-1) W
  have honeNeg : hsDistSq Y (1 : Matrix Y Y ℂ) (-1) = 4 :=
    hsDistSq_one_neg_one Y hY
  rw [honeNeg, hsDistSq_comm Y 1 M] at htriangle₁
  nlinarith

/-- Every sequential operator-norm almost representation in which the marked
word stays uniformly separated from the identity is impossible.  Cutting the
central involution to its negative spectral sector reduces this to
`false_of_marked_word_tends_to_neg_one`. -/
theorem false_of_markedOpAlmostRepresentation
    (D : MarkedCompressionInclusionData Γ E)
    (A : MarkedOpAlmostRepresentation E D.word) : False := by
  have hz : D.word * D.word = 1 := by
    have h := D.word_pow_two
    rwa [pow_two] at h
  have hcentral : ∀ g : E, D.word * g = g * D.word := fun g ↦
    (D.word_commute g).eq
  have hsep : ∃ N, ∀ n ≥ N, A.separation ≤
      ‖(A.toOpAlmostRepresentation.map n D.word :
        Matrix (A.toOpAlmostRepresentation.model n)
          (A.toOpAlmostRepresentation.model n) ℂ) -
        A.toOpAlmostRepresentation.map n 1‖ :=
    ⟨0, fun n _ ↦ A.marked_separated n⟩
  obtain ⟨B, hnegative⟩ :=
    NegativeCornerModel.exists_negativeCorner_opAlmostRepresentation
      A.toOpAlmostRepresentation hz hcentral A.separation_pos hsep
  exact false_of_marked_word_tends_to_neg_one B D hnegative

end KazhdanCompressorCorner

/-! ## Arbitrary-ultraproduct and weak-MF endpoints -/

namespace MarkedCompressionInclusionData

open KazhdanCompressorCorner

variable {E : Type u} [Group E]

/-- The marked word is killed by every homomorphism into every operator-norm
matrix ultraproduct.  Countability is used only to extract a sequential
marked almost representation from an arbitrary ultrafilter. -/
theorem word_normMFInvisible [Countable E]
    (D : MarkedCompressionInclusionData Γ E) : NormMFInvisible D.word :=
  normMFInvisible_of_no_markedOpAlmostRepresentation
    (false_of_markedOpAlmostRepresentation D)

/-- A countable marked-compression group with nontrivial marked word is not
weak/operator-norm MF. -/
theorem not_isWeakMF [Countable E]
    (D : MarkedCompressionInclusionData Γ E) (hne : D.word ≠ 1) :
    ¬ IsWeakMF E :=
  not_isWeakMF_of_normMFInvisible D.word_normMFInvisible hne

/-- Package the proved kill theorem with a nontriviality witness as the
marked-compression certificate. -/
noncomputable def normCertificate [Countable E]
    (D : MarkedCompressionInclusionData Γ E) (hne : D.word ≠ 1) :
    MarkedCompressionNormCertificate E :=
  ⟨D.t, D.iota D.a, D.c, hne, D.word_normMFInvisible⟩

end MarkedCompressionInclusionData

end GroupApproximation
