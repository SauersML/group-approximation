import GroupApproximation.Leavitt.ProperlyInfiniteUnit
import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted
import GroupApproximation.Meta.AxiomGuard

/-!
# Three printed steps of `sec:one-sided-inverses` (tex 809–925)

`non_mf_groups_exist.tex`, Lemma `lem:two-copies` and Lemma `lem:ring-compression-cell`.  The
census rows of three sentences named carriers that state less than the printed sentence:

* `PrintedTwoCopiesConverse` (tex 812–813, the statement of `lem:two-copies`):
  > Conversely, such elements satisfy `w₀v₀=1` and `w₁(1-v₀w₀)v₁=1`.

  `RankDescentPrinted.PrintedTwoCopiesLemma` states the converse only as "some `s, t` with
  `ts = 1` have a full complementary idempotent".  Here both printed identities are stated for the
  given elements, and the second is proved along the printed computation
  `w₁(1-v₀w₀)v₁ = w₁v₁ - (w₁v₀)(w₀v₁)` (tex 827–828).
* `PrintedTwoCopiesFourEquations` (tex 825–827, proof of `lem:two-copies`):
  > So `w₀v₀=tᵐsᵐ=1`, `w₁v₁=∑ⱼaⱼebⱼ=1`, `w₀v₁=∑ⱼt^{m-j}ebⱼ=0`, and `w₁v₀=∑ⱼaⱼes^{m-j}=0`.

  The existing carriers `RankDescent.full_*` state only the four end values.  Here every printed
  middle sum is stated.
* `PrintedCompressorMarkProducts` (tex 918–922, proof of `lem:ring-compression-cell`):
  > Both `uc` and `e₁₂(e)u` equal `u+etE₁₄`: the last column of `uc` is `(e,et,et²,t³)ᵀ(1+et)` and
  > `e²=e`, `te=0`, while `e₁₂(e)u` adds `e` times the second row `(0,s,0,et)` of `u` to its first
  > row, and `es=0`.

  `OneSidedCompressor.compressor_mul_centralMark` proves `uc = e₁₂(e)u` in one entrywise
  computation.  Here the common value `u + etE₁₄` and the two printed reasons are stated.

Coordinates are 0-indexed: the printed `E₁₄` is `Matrix.single 0 3` and `e₁₂` is
`Matrix.single 0 1`.  Every statement is for every unital ring `R` and every pair `s, t ∈ R` with
`ts = 1`, which is `P : OneSidedInverse R`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace OneSidedInversesPrintedSteps

open OneSidedCompressor
open Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted

/-! ## `lem:two-copies` -/

/-- **Printed sentence** (tex 812–813, the statement of `lem:two-copies`).

> Conversely, such elements satisfy `w₀v₀=1` and `w₁(1-v₀w₀)v₁=1`.

"Such elements" are any `v₀, v₁, w₀, w₁ ∈ R` with `wᵢvⱼ = δᵢⱼ`. -/
def PrintedTwoCopiesConverse : Prop :=
  ∀ (R : Type) [Ring R] (v w : Fin 2 → R),
    (∀ i j, w i * v j = if i = j then 1 else 0) →
      w 0 * v 0 = 1 ∧ w 1 * (1 - v 0 * w 0) * v 1 = 1

theorem printedTwoCopiesConverse : PrintedTwoCopiesConverse := by
  intro R _ v w hvw
  have hne : (1 : Fin 2) ≠ 0 := by decide
  have h00 : w 0 * v 0 = 1 := by simpa using hvw 0 0
  have h10 : w 1 * v 0 = 0 := by simpa [hne] using hvw 1 0
  have h11 : w 1 * v 1 = 1 := by simpa using hvw 1 1
  refine ⟨h00, ?_⟩
  calc w 1 * (1 - v 0 * w 0) * v 1
      = w 1 * v 1 - (w 1 * v 0) * (w 0 * v 1) := by noncomm_ring
    _ = 1 := by rw [h10, h11, zero_mul, sub_zero]

section TwoCopiesSteps

variable {R : Type} [Ring R] (P : OneSidedInverse R) {m : ℕ}

/-- `w₀v₁ = ∑ⱼ t^{m-j} e bⱼ` (tex 826): `tᵐsʲ = t^{m-j}` for `j < m`. -/
theorem w0_mul_v1_eq_sum (b : Fin m → R) :
    P.t ^ m * (∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k)
      = ∑ k : Fin m, P.t ^ (m - (k : ℕ)) * P.e * b k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h := RankDescent.t_pow_mul_s_pow_of_ge P (le_of_lt k.isLt)
  calc P.t ^ m * (P.s ^ (k : ℕ) * P.e * b k)
      = P.t ^ m * P.s ^ (k : ℕ) * P.e * b k := by noncomm_ring
    _ = P.t ^ (m - (k : ℕ)) * P.e * b k := by rw [h]

/-- `∑ⱼ t^{m-j} e bⱼ = 0` (tex 826): each exponent `m - j` is positive, and `te = 0`. -/
theorem sum_t_pow_sub_mul_e_eq_zero (b : Fin m → R) :
    ∑ k : Fin m, P.t ^ (m - (k : ℕ)) * P.e * b k = 0 := by
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  obtain ⟨d, hd⟩ : ∃ d, m - (k : ℕ) = d + 1 := ⟨m - (k : ℕ) - 1, by omega⟩
  rw [hd, P.t_pow_mul_e, zero_mul]

/-- `w₁v₀ = ∑ⱼ aⱼ e s^{m-j}` (tex 827): `tʲsᵐ = s^{m-j}` for `j < m`. -/
theorem w1_mul_v0_eq_sum (a : Fin m → R) :
    (∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)) * P.s ^ m
      = ∑ k : Fin m, a k * P.e * P.s ^ (m - (k : ℕ)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h := RankDescent.t_pow_mul_s_pow_of_le P (le_of_lt k.isLt)
  calc a k * P.e * P.t ^ (k : ℕ) * P.s ^ m
      = a k * P.e * (P.t ^ (k : ℕ) * P.s ^ m) := by noncomm_ring
    _ = a k * P.e * P.s ^ (m - (k : ℕ)) := by rw [h]

/-- `∑ⱼ aⱼ e s^{m-j} = 0` (tex 827): each exponent `m - j` is positive, and `es = 0`. -/
theorem sum_e_mul_s_pow_sub_eq_zero (a : Fin m → R) :
    ∑ k : Fin m, a k * P.e * P.s ^ (m - (k : ℕ)) = 0 := by
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  obtain ⟨d, hd⟩ : ∃ d, m - (k : ℕ) = d + 1 := ⟨m - (k : ℕ) - 1, by omega⟩
  rw [hd, mul_assoc, P.e_mul_s_pow, mul_zero]

/-- `w₁v₁ = ∑ⱼ aⱼ e bⱼ` (tex 826): the orthogonality `e tⁱ sʲ e = δᵢⱼ e` (tex 823) collapses the
double sum to its diagonal. -/
theorem w1_mul_v1_eq_sum (a b : Fin m → R) :
    (∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)) *
        (∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k)
      = ∑ k : Fin m, a k * P.e * b k := by
  rw [Finset.sum_mul_sum]
  have key : ∀ i j : Fin m,
      (a i * P.e * P.t ^ (i : ℕ)) * (P.s ^ (j : ℕ) * P.e * b j)
        = if i = j then a i * P.e * b i else 0 := by
    intro i j
    have h := RankDescent.e_mul_t_pow_mul_s_pow_mul_e P (i : ℕ) (j : ℕ)
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl] at h ⊢
      calc a i * P.e * P.t ^ (i : ℕ) * (P.s ^ (i : ℕ) * P.e * b i)
          = a i * (P.e * P.t ^ (i : ℕ) * P.s ^ (i : ℕ) * P.e) * b i := by
            noncomm_ring
        _ = a i * P.e * b i := by rw [h]
    · have hne : ¬ ((i : ℕ) = (j : ℕ)) := fun hc ↦ hij (Fin.ext hc)
      rw [if_neg hne] at h
      rw [if_neg hij]
      calc a i * P.e * P.t ^ (i : ℕ) * (P.s ^ (j : ℕ) * P.e * b j)
          = a i * (P.e * P.t ^ (i : ℕ) * P.s ^ (j : ℕ) * P.e) * b j := by
            noncomm_ring
        _ = 0 := by rw [h]; noncomm_ring
  simp only [key]
  simp

end TwoCopiesSteps

/-- **Printed sentence** (tex 825–827, proof of `lem:two-copies`).

> So `w₀v₀=tᵐsᵐ=1`, `w₁v₁=∑ⱼaⱼebⱼ=1`, `w₀v₁=∑ⱼt^{m-j}ebⱼ=0`, and `w₁v₀=∑ⱼaⱼes^{m-j}=0`.

Here `v₀ = sᵐ`, `w₀ = tᵐ`, `v₁ = ∑ⱼ sʲebⱼ`, `w₁ = ∑ⱼ aⱼetʲ` (tex 821, the fields of
`RankDescent.ofFull`), `e = 1 - st`, and `∑ⱼ aⱼebⱼ = 1` is the fullness witness (tex 818–819).
Each printed chain is stated link by link. -/
def PrintedTwoCopiesFourEquations : Prop :=
  ∀ (R : Type) [Ring R] (P : OneSidedInverse R) (m : ℕ) (a b : Fin m → R),
    ∑ k : Fin m, a k * P.e * b k = 1 →
      P.t ^ m * P.s ^ m = 1 ∧
      ((∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)) *
            (∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k) = ∑ k : Fin m, a k * P.e * b k ∧
          ∑ k : Fin m, a k * P.e * b k = 1) ∧
      (P.t ^ m * (∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k) =
            ∑ k : Fin m, P.t ^ (m - (k : ℕ)) * P.e * b k ∧
          ∑ k : Fin m, P.t ^ (m - (k : ℕ)) * P.e * b k = 0) ∧
      ((∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)) * P.s ^ m =
            ∑ k : Fin m, a k * P.e * P.s ^ (m - (k : ℕ)) ∧
          ∑ k : Fin m, a k * P.e * P.s ^ (m - (k : ℕ)) = 0)

theorem printedTwoCopiesFourEquations : PrintedTwoCopiesFourEquations := by
  intro R _ P m a b hab
  exact ⟨RankDescent.t_pow_mul_s_pow_self P m,
    ⟨w1_mul_v1_eq_sum P a b, hab⟩,
    ⟨w0_mul_v1_eq_sum P b, sum_t_pow_sub_mul_e_eq_zero P b⟩,
    ⟨w1_mul_v0_eq_sum P a, sum_e_mul_s_pow_sub_eq_zero P a⟩⟩

/-! ## `lem:ring-compression-cell` -/

section CompressorMark

variable {R : Type} [Ring R] (P : OneSidedInverse R)

/-- `uc = u + etE₁₄` (tex 918–920). -/
theorem compressorMatrix_mul_centralMarkMatrix :
    compressorMatrix P * centralMarkMatrix P
      = compressorMatrix P + Matrix.single 0 3 (P.e * P.t) := by
  have hee : ∀ x : R, P.e * (P.e * x) = P.e * x := fun x ↦ by
    rw [← mul_assoc, P.e_mul_e]
  have hte : ∀ x : R, P.t * (P.e * x) = 0 := fun x ↦ by
    rw [← mul_assoc, P.t_mul_e, zero_mul]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [compressorMatrix, centralMarkMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      mul_add, mul_assoc, hee, hte]

/-- `e₁₂(e)u = u + etE₁₄` (tex 920–922). -/
theorem elementaryMatrix_mul_compressorMatrix :
    (1 + Matrix.single 0 1 P.e) * compressorMatrix P
      = compressorMatrix P + Matrix.single 0 3 (P.e * P.t) := by
  have hee : ∀ x : R, P.e * (P.e * x) = P.e * x := fun x ↦ by
    rw [← mul_assoc, P.e_mul_e]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [compressorMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hee]

/-- The last column of `uc` is the last column `(e, et, et², t³)ᵀ` of `u` times `1 + et`
(tex 919–920). -/
theorem compressorMatrix_mul_centralMarkMatrix_lastCol (i : Fin 4) :
    (compressorMatrix P * centralMarkMatrix P) i 3
      = compressorMatrix P i 3 * (1 + P.e * P.t) := by
  fin_cases i <;>
    simp [compressorMatrix, centralMarkMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- `e₁₂(e)u` adds `e` times the second row `(0, s, 0, et)` of `u` to its first row
(tex 920–922). -/
theorem elementaryMatrix_mul_compressorMatrix_firstRow (j : Fin 4) :
    ((1 + Matrix.single 0 1 P.e : Matrix (Fin 4) (Fin 4) R) * compressorMatrix P) 0 j
      = compressorMatrix P 0 j + P.e * compressorMatrix P 1 j := by
  fin_cases j <;>
    simp [compressorMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

end CompressorMark

/-- **Printed sentence** (tex 918–922, proof of `lem:ring-compression-cell`).

> Both `uc` and `e₁₂(e)u` equal `u+etE₁₄`: the last column of `uc` is `(e,et,et²,t³)ᵀ(1+et)` and
> `e²=e`, `te=0`, while `e₁₂(e)u` adds `e` times the second row `(0,s,0,et)` of `u` to its first
> row, and `es=0`.

`u` is `compressor P` with matrix `compressorMatrix P`, `c` is `centralMark P` with matrix
`centralMarkMatrix P = diag(1,1,1,1+et)`, and `e₁₂(e)` is the root on coordinates `(1,2)`. -/
def PrintedCompressorMarkProducts : Prop :=
  ∀ (R : Type) [Ring R] (P : OneSidedInverse R),
    (↑(↑(compressor P * centralMark P) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
          Matrix (Fin 4) (Fin 4) R) =
        compressorMatrix P + Matrix.single 0 3 (P.e * P.t) ∧
      (↑(↑(elementaryRoot (coreIdx 0) (coreIdx 1) (coreIdx_injective.ne zeroNeOne) P.e *
              compressor P) : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) =
        compressorMatrix P + Matrix.single 0 3 (P.e * P.t) ∧
      (∀ i : Fin 4, (compressorMatrix P * centralMarkMatrix P) i 3 =
        compressorMatrix P i 3 * (1 + P.e * P.t)) ∧
      ∀ j : Fin 4, ((1 + Matrix.single 0 1 P.e : Matrix (Fin 4) (Fin 4) R) * compressorMatrix P) 0 j =
        compressorMatrix P 0 j + P.e * compressorMatrix P 1 j

theorem printedCompressorMarkProducts : PrintedCompressorMarkProducts := by
  intro R _ P
  refine ⟨?_, ?_, compressorMatrix_mul_centralMarkMatrix_lastCol P,
    elementaryMatrix_mul_compressorMatrix_firstRow P⟩
  · show matOf (compressor P * centralMark P) = _
    rw [matOf_mul, matOf_eq (compressor P), matOf_eq (centralMark P), compressor_val,
      centralMark_val]
    exact compressorMatrix_mul_centralMarkMatrix P
  · show matOf (elementaryRoot (coreIdx 0) (coreIdx 1) (coreIdx_injective.ne zeroNeOne) P.e *
      compressor P) = _
    rw [matOf_mul, matOf_elementaryRoot, matOf_eq (compressor P), compressor_val]
    exact elementaryMatrix_mul_compressorMatrix P

end OneSidedInversesPrintedSteps
end NonMFSentences
end Manuscript
end GroupApproximation

#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.printedTwoCopiesConverse
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.printedTwoCopiesFourEquations
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.printedCompressorMarkProducts
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.w0_mul_v1_eq_sum
#audit_axioms
  GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.sum_t_pow_sub_mul_e_eq_zero
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.w1_mul_v0_eq_sum
#audit_axioms
  GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.sum_e_mul_s_pow_sub_eq_zero
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.w1_mul_v1_eq_sum
#audit_axioms
  GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.compressorMatrix_mul_centralMarkMatrix
#audit_axioms
  GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.elementaryMatrix_mul_compressorMatrix
#audit_axioms
  GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.compressorMatrix_mul_centralMarkMatrix_lastCol
#audit_axioms
  GroupApproximation.Manuscript.NonMFSentences.OneSidedInversesPrintedSteps.elementaryMatrix_mul_compressorMatrix_firstRow
