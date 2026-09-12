import GroupApproximation.Analysis.OperatorNormCertificate
import Mathlib.LinearAlgebra.Matrix.Hermitian
import GroupApproximation.Analysis.UnitaryPerturbation

/-!
# Rational Hermitian matrices are dense

The Cayley transform is Lipschitz on Hermitian matrices, so a dense set of
Hermitian parameters gives a dense set of unitaries.  This file supplies the
parameters: matrices whose entries have rational real and imaginary parts are
dense in the Hermitian matrices, for the trivial reason that the rationals are
dense in the reals.

The only care needed is that rounding entrywise destroys Hermitian symmetry.
It is restored by symmetrising, `Q ↦ (Q + Qᴴ) / 2`, which stays inside the
rational entries because the rationals are closed under the operations
involved, and which does not spoil the estimate because the original matrix is
already its own symmetrisation.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace RationalHermitian

open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-- A complex number with rational real and imaginary parts. -/
def ofRatPair (q : ℚ × ℚ) : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

@[simp] theorem ofRatPair_re (q : ℚ × ℚ) : (ofRatPair q).re = (q.1 : ℝ) := by
  simp [ofRatPair]

@[simp] theorem ofRatPair_im (q : ℚ × ℚ) : (ofRatPair q).im = (q.2 : ℝ) := by
  simp [ofRatPair]

/-- A complex matrix with rational entries. -/
def ofRat {n : Type*} (Q : Matrix n n (ℚ × ℚ)) : Matrix n n ℂ :=
  fun i j => ofRatPair (Q i j)

/-! ## Entrywise approximation -/

theorem exists_rat_pair_close (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ × ℚ, ‖z - ofRatPair q‖ < δ := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - δ / 2 < z.re + δ / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - δ / 2 < z.im + δ / 2 by linarith)
  refine ⟨(a, b), ?_⟩
  have hre : |(z - ofRatPair (a, b)).re| < δ / 2 := by
    have hval : (z - ofRatPair (a, b)).re = z.re - (a : ℝ) := by simp
    rw [hval, abs_lt]
    constructor <;> linarith
  have him : |(z - ofRatPair (a, b)).im| < δ / 2 := by
    have hval : (z - ofRatPair (a, b)).im = z.im - (b : ℝ) := by simp
    rw [hval, abs_lt]
    constructor <;> linarith
  have hbound := Complex.norm_le_abs_re_add_abs_im (z - ofRatPair (a, b))
  linarith

/-! ## Symmetrisation -/

/-- The rational symmetrisation of a rational matrix. -/
def symmetrise {n : Type*} (Q : Matrix n n (ℚ × ℚ)) : Matrix n n (ℚ × ℚ) :=
  fun i j => (((Q i j).1 + (Q j i).1) / 2, ((Q i j).2 - (Q j i).2) / 2)

theorem isHermitian_ofRat_symmetrise {n : Type*} (Q : Matrix n n (ℚ × ℚ)) :
    Matrix.IsHermitian (ofRat (symmetrise Q)) := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  apply Complex.ext
  · simp only [RCLike.star_def, Complex.conj_re, ofRat, symmetrise,
      ofRatPair_re]
    push_cast
    ring
  · simp only [RCLike.star_def, Complex.conj_im, ofRat, symmetrise,
      ofRatPair_im]
    push_cast
    ring

/-- The symmetrised entry, as an average with a conjugate. -/
theorem ofRatPair_symmetrise {n : Type*} (Q : Matrix n n (ℚ × ℚ)) (i j : n) :
    ofRatPair (symmetrise Q i j)
      = (ofRatPair (Q i j) + (starRingEnd ℂ) (ofRatPair (Q j i))) / 2 := by
  apply Complex.ext
  · simp only [symmetrise, ofRatPair_re, Complex.div_re, Complex.add_re,
      Complex.conj_re, Complex.normSq_ofNat]
    push_cast
    simp
    ring
  · simp only [symmetrise, ofRatPair_im, Complex.div_im, Complex.add_im,
      Complex.conj_im, Complex.normSq_ofNat]
    push_cast
    simp
    ring

/-! ## The density statement -/

/-- **Rational Hermitian matrices are dense in the Hermitian matrices.** -/
theorem exists_rat_hermitian_close {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Matrix n n (ℚ × ℚ), Matrix.IsHermitian (ofRat Q) ∧
      ‖H - ofRat Q‖ < ε := by
  classical
  set N : ℝ := (Fintype.card n : ℝ) with hN
  set δ : ℝ := ε / (2 * (N ^ 2 + 1)) with hδdef
  have hpos : (0 : ℝ) < 2 * (N ^ 2 + 1) := by rw [hN]; positivity
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hchoice : ∀ i j : n, ∃ q : ℚ × ℚ, ‖H i j - ofRatPair q‖ < δ :=
    fun i j => exists_rat_pair_close (H i j) hδ
  choose q hq using hchoice
  refine ⟨symmetrise q, isHermitian_ofRat_symmetrise q, ?_⟩
  have hHsym : ∀ i j : n, H i j = (starRingEnd ℂ) (H j i) := by
    intro i j
    have h := congrFun (congrFun hH i) j
    rw [Matrix.conjTranspose_apply, RCLike.star_def] at h
    exact h.symm
  have hentry : ∀ i j : n, ‖(H - ofRat (symmetrise q)) i j‖ ≤ δ := by
    intro i j
    have hij := hq i j
    have hji := hq j i
    have hsplit : (H - ofRat (symmetrise q)) i j
        = ((H i j - ofRatPair (q i j))
            + (starRingEnd ℂ) (H j i - ofRatPair (q j i))) / 2 := by
      have hH2 : (starRingEnd ℂ) (H j i) = H i j := (hHsym i j).symm
      rw [Matrix.sub_apply, ofRat, ofRatPair_symmetrise, map_sub, hH2]
      ring
    rw [hsplit, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    have htri : ‖(H i j - ofRatPair (q i j))
        + (starRingEnd ℂ) (H j i - ofRatPair (q j i))‖ ≤ 2 * δ := by
      refine (norm_add_le _ _).trans ?_
      have hconj : ‖(starRingEnd ℂ) (H j i - ofRatPair (q j i))‖
          = ‖H j i - ofRatPair (q j i)‖ := by
        rw [← RCLike.star_def, norm_star]
      rw [hconj]
      linarith
    linarith
  have hbound : ‖H - ofRat (symmetrise q)‖ ≤ N ^ 2 * δ :=
    OperatorNormCertificate.opNorm_le_of_entry_bound _ hδ.le hentry
  have hfinal : N ^ 2 * δ < ε := by
    rw [hδdef]
    have hNsq : (0 : ℝ) ≤ N ^ 2 := by positivity
    rw [mul_div_assoc']
    rw [div_lt_iff₀ hpos]
    nlinarith
  linarith

/-! ## Rational Cayley transforms are dense

Combining the three estimates: a unitary is near a Cayley transform, its
Hermitian parameter is near a rational one, and the Cayley transform is
Lipschitz. -/

/-- **Every unitary is approximated by the Cayley transform of a matrix with
rational entries.**

This is the density statement the arithmetical route needs on the microstate
side: the parameters range over a countable set that carries an explicit
encoding, and the transform of each is exactly unitary. -/
theorem exists_rat_cayley_close {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Matrix n n (ℚ × ℚ), Matrix.IsHermitian (ofRat Q) ∧
      ‖U - CayleyUnitary.cayley (ofRat Q)‖ < ε := by
  obtain ⟨H, hH, hHclose⟩ :=
    UnitaryPerturbation.exists_hermitian_cayley_close hU (by positivity : 0 < ε / 2)
  obtain ⟨Q, hQ, hQclose⟩ :=
    exists_rat_hermitian_close hH (by positivity : 0 < ε / 8)
  refine ⟨Q, hQ, ?_⟩
  have hlip : ‖CayleyUnitary.cayley H - CayleyUnitary.cayley (ofRat Q)‖
      ≤ 2 * ‖H - ofRat Q‖ :=
    CayleyUnitary.norm_cayley_sub_cayley hH hQ
  have htri : ‖U - CayleyUnitary.cayley (ofRat Q)‖
      ≤ ‖U - CayleyUnitary.cayley H‖
        + ‖CayleyUnitary.cayley H - CayleyUnitary.cayley (ofRat Q)‖ := by
    have hsplit : U - CayleyUnitary.cayley (ofRat Q)
        = (U - CayleyUnitary.cayley H)
          + (CayleyUnitary.cayley H - CayleyUnitary.cayley (ofRat Q)) := by
      abel
    rw [hsplit]
    exact norm_add_le _ _
  linarith

end RationalHermitian
end GroupApproximation
