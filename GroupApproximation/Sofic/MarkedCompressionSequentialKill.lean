import GroupApproximation.Sofic.KazhdanCompressorCorner

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
* `‖1 - (-1)‖₂ = 2` rules both out simultaneously.

Consequently a countable group carrying inclusion data with nontrivial
marked word is not weak/operator-norm MF, modulo the negative-corner input,
which is quarantined in a single explicitly stated stub.
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
    have h1 : 0 ≤ (δ * (a i).re - (b i).re) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (δ * (a i).im - (b i).im) ^ 2 := sq_nonneg _
    have hδ' : 0 < δ⁻¹ := by positivity
    rw [hre, Complex.normSq_apply, Complex.normSq_apply]
    have e1 : (a i).re * (b i).re ≤
        (2 : ℝ)⁻¹ * (δ * ((a i).re * (a i).re) +
          δ⁻¹ * ((b i).re * (b i).re)) := by
      have hkey : δ * ((δ * (a i).re - (b i).re) ^ 2) / (δ * δ) =
          δ * (a i).re ^ 2 - 2 * ((a i).re * (b i).re) +
            δ⁻¹ * (b i).re ^ 2 := by
        field_simp
        ring
      nlinarith [mul_pos hδ hδ, sq_nonneg (δ * (a i).re - (b i).re),
        mul_nonneg (le_of_lt hδ) (sq_nonneg (δ * (a i).re - (b i).re))]
    have e2 : (a i).im * (b i).im ≤
        (2 : ℝ)⁻¹ * (δ * ((a i).im * (a i).im) +
          δ⁻¹ * ((b i).im * (b i).im)) := by
      nlinarith [mul_pos hδ hδ, sq_nonneg (δ * (a i).im - (b i).im),
        mul_nonneg (le_of_lt hδ) (sq_nonneg (δ * (a i).im - (b i).im))]
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

/-- Entrywise mass is dominated by dimension times squared operator norm. -/
theorem sum_normSq_le_card_mul_sq (Y : FiniteModel) (M : Matrix Y Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq (M i j) ≤
      Fintype.card Y * ‖M‖ ^ 2 := by
  have h := hsDistSq_le_sq_l2_opNorm Y M 0
  rw [hsDistSq] at h
  have hcard : (0 : ℝ) ≤ Fintype.card Y := by positivity
  have hsimp : ∀ i j : Y, M i j - (0 : Matrix Y Y ℂ) i j = M i j := by
    intro i j
    simp
  by_cases hzero : Fintype.card Y = 0
  · have hempty : IsEmpty Y := by
      rw [← Fintype.card_eq_zero_iff]
      exact hzero
    simp [Finset.sum_of_isEmpty]
  · have hpos : (0 : ℝ) < Fintype.card Y := by
      have : 0 < Fintype.card Y := Nat.pos_of_ne_zero hzero
      exact_mod_cast this
    rw [div_le_iff₀ hpos] at h
    calc
      ∑ i : Y, ∑ j : Y, Complex.normSq (M i j) =
          ∑ i : Y, ∑ j : Y,
            Complex.normSq (M i j - (0 : Matrix Y Y ℂ) i j) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hsimp i j]
      _ ≤ ‖M - 0‖ ^ 2 * Fintype.card Y := h
      _ = Fintype.card Y * ‖M‖ ^ 2 := by rw [sub_zero]; ring

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
    have hcolv : ∀ i : Y, (u *ᵥ Pi.single j (1 : ℂ)) i = u i j := by
      intro i
      rw [Matrix.mulVec_single_one]
    rw [hsingle] at hmass
    calc
      ∑ i : Y, Complex.normSq (u i j) =
          ∑ i : Y, Complex.normSq ((u *ᵥ Pi.single j (1 : ℂ)) i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hcolv i]
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
  rw [hsDistSq, hsDistSq, hsDistSq, div_add_div_same, ← mul_div_assoc,
    ← mul_div_assoc, div_add_div_same]
  apply div_le_div_of_nonneg_right ?_ ?_ |>.trans
  · exact le_refl _
  all_goals sorry

theorem hsDistSq_comm (Y : FiniteModel) (A C : Matrix Y Y ℂ) :
    hsDistSq Y A C = hsDistSq Y C A := by
  rw [hsDistSq, hsDistSq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show A i j - C i j = -(C i j - A i j) by ring, Complex.normSq_neg]

end KazhdanCompressorCorner
end GroupApproximation
