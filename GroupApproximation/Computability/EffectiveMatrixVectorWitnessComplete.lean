import GroupApproximation.Analysis.RationalHermitian
import GroupApproximation.Computability.EffectiveMatrixCode

/-!
# Completeness of the executable lower-norm witness

`EffectiveMatrixCode.vectorWitness` is already proved sound.  Here we prove
the converse needed by the arithmetical MF checker: if the interpreted matrix
has operator norm strictly larger than `1/3`, then a Gaussian-rational vector
code witnesses that inequality.

The proof first extracts a vector on which the strict operator-norm inequality
is visible.  Gaussian-rational coordinate vectors are dense, and the strict
inequality survives a sufficiently small perturbation.
-/

namespace GroupApproximation
namespace EffectiveMatrixVectorWitnessComplete

open scoped Matrix
open scoped Matrix.Norms.L2Operator

open RationalComplexCode EffectiveMatrixCode

noncomputable section

/-- Gaussian-rational coordinate vectors are dense in a finite-dimensional
Euclidean space, stated directly in the executable vector-code syntax. -/
theorem exists_vectorCode_close (d : ℕ)
    (x : EuclideanSpace ℂ (Fin (dim d))) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : VectorCode,
      ‖x - (EuclideanSpace.equiv (Fin (dim d)) ℂ).symm (toVector d v)‖ < ε := by
  classical
  let D : ℝ := dim d
  have hD : 0 < D := by simp only [D, dim, Nat.cast_add, Nat.cast_one]; positivity
  let δ : ℝ := ε / D
  have hδ : 0 < δ := div_pos hε hD
  have hchoice : ∀ i : Fin (dim d), ∃ z : ComplexCode,
      ‖x i - toComplex z‖ < δ := by
    intro i
    obtain ⟨q, hq⟩ := RationalHermitian.exists_rat_pair_close (x i) hδ
    obtain ⟨z, hz⟩ := exists_toComplex_of_ratPair q
    exact ⟨z, by rwa [hz]⟩
  choose z hz using hchoice
  let v : VectorCode := List.ofFn z
  let y : EuclideanSpace ℂ (Fin (dim d)) :=
    (EuclideanSpace.equiv (Fin (dim d)) ℂ).symm (toVector d v)
  have hy (i : Fin (dim d)) : y i = toComplex (z i) := by
    simp [y, v, toVector, vectorEntry]
  have hcoord (i : Fin (dim d)) : ‖(x - y) i‖ < δ := by
    change ‖x i - y i‖ < δ
    rw [hy]
    exact hz i
  let i₀ : Fin (dim d) := ⟨0, by simp [dim]⟩
  have hcoordSq (i : Fin (dim d)) : ‖(x - y) i‖ ^ 2 < δ ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hδ).2 (hcoord i)
  have hsum : ∑ i : Fin (dim d), ‖(x - y) i‖ ^ 2 <
      ∑ _i : Fin (dim d), δ ^ 2 := by
    exact Finset.sum_lt_sum (fun i _ ↦ (hcoordSq i).le)
      ⟨i₀, Finset.mem_univ _, hcoordSq i₀⟩
  have hsum' : ∑ i : Fin (dim d), ‖(x - y) i‖ ^ 2 < ε ^ 2 := by
    calc
      ∑ i : Fin (dim d), ‖(x - y) i‖ ^ 2
          < ∑ _i : Fin (dim d), δ ^ 2 := hsum
      _ = D * δ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp [D]
      _ ≤ ε ^ 2 := by
        have hDone : 1 ≤ D := by
          exact_mod_cast (Nat.succ_le_iff.2 (Nat.zero_lt_succ d))
        dsimp [δ]
        field_simp
        nlinarith [sq_nonneg ε]
  refine ⟨v, ?_⟩
  rw [show (EuclideanSpace.equiv (Fin (dim d)) ℂ).symm (toVector d v) = y from rfl,
    EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ i : Fin (dim d), ‖(x - y) i‖ ^ 2)
        < Real.sqrt (ε ^ 2) := (Real.sqrt_lt_sqrt (by positivity)).2 hsum'
    _ = ε := Real.sqrt_sq_eq_abs _ |>.trans (abs_of_pos hε)

/-- A vector-code norm inequality is exactly strong enough to pass the
executable `vectorWitness` test. -/
theorem vectorWitness_of_norm_sq_lt (d : ℕ) (A : MatrixCode) (v : VectorCode)
    (h : ‖(EuclideanSpace.equiv (Fin (dim d)) ℂ).symm (toVector d v)‖ ^ 2 <
      9 * ‖Matrix.toEuclideanCLM (n := Fin (dim d)) (𝕜 := ℂ) (toMatrix d A)
        ((EuclideanSpace.equiv (Fin (dim d)) ℂ).symm (toVector d v))‖ ^ 2) :
    vectorWitness d A v := by
  rw [vectorWitness, ratLt_iff]
  have hreal :
      ((toRat (vectorNormSq d v) : ℚ) : ℝ) <
        ((toRat (ratMul (ratOfNat 9) (mulVecNormSq d A v)) : ℚ) : ℝ) := by
    rw [toRat_mul, toRat_ratOfNat]
    push_cast
    rw [vectorNormSq_semantics, mulVecNormSq_semantics]
    simpa only [EuclideanSpace.norm_sq_eq, Equiv.apply_symm_apply,
      OperatorNormCertificate.apply_coord] using h
  exact_mod_cast hreal

/-- **Completeness of the executable lower-bound witness.**  Every coded
matrix whose interpreted operator norm is strictly greater than `1/3` admits a
Gaussian-rational vector certificate accepted by `vectorWitness`. -/
theorem exists_vectorWitness_of_one_third_lt_opNorm (d : ℕ) (A : MatrixCode)
    (hA : (1 : ℝ) / 3 < ‖toMatrix d A‖) :
    ∃ v : VectorCode, vectorWitness d A v := by
  let T := Matrix.toEuclideanCLM (n := Fin (dim d)) (𝕜 := ℂ) (toMatrix d A)
  have hex : ∃ x : EuclideanSpace ℂ (Fin (dim d)),
      (1 / 3 : ℝ) * ‖x‖ < ‖T x‖ := by
    by_contra hn
    push Not at hn
    have hbound : ‖T‖ ≤ (1 / 3 : ℝ) :=
      ContinuousLinearMap.opNorm_le_bound T (by norm_num) hn
    rw [Matrix.cstar_norm_def] at hA
    exact (not_lt_of_ge hbound) hA
  obtain ⟨x, hx⟩ := hex
  let m : ℝ := ‖T x‖ - (1 / 3 : ℝ) * ‖x‖
  have hm : 0 < m := sub_pos.2 hx
  let ε : ℝ := m / (2 * (‖T‖ + 4 / 3))
  have hden : 0 < 2 * (‖T‖ + 4 / 3) := by positivity
  have hε : 0 < ε := div_pos hm hden
  obtain ⟨v, hv⟩ := exists_vectorCode_close d x hε
  let y : EuclideanSpace ℂ (Fin (dim d)) :=
    (EuclideanSpace.equiv (Fin (dim d)) ℂ).symm (toVector d v)
  have hTy : ‖T x‖ - ‖T‖ * ‖x - y‖ ≤ ‖T y‖ := by
    have htri := norm_sub_norm_le (T x) (T y)
    have hmap : ‖T x - T y‖ ≤ ‖T‖ * ‖x - y‖ := by
      rw [← map_sub]
      exact ContinuousLinearMap.le_opNorm T (x - y)
    linarith
  have hy : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have := norm_sub_norm_le y x
    rw [norm_sub_rev] at this
    linarith
  have hmargin : (‖T‖ + 1 / 3) * ‖x - y‖ < m := by
    have hcoef : ‖T‖ + 1 / 3 < 2 * (‖T‖ + 4 / 3) := by
      have := norm_nonneg T
      linarith
    calc
      (‖T‖ + 1 / 3) * ‖x - y‖
          < (‖T‖ + 1 / 3) * ε :=
            mul_lt_mul_of_pos_left hv (by positivity)
      _ < (2 * (‖T‖ + 4 / 3)) * ε :=
            mul_lt_mul_of_pos_right hcoef hε
      _ = m := by dsimp [ε]; field_simp
  have hratio : (1 / 3 : ℝ) * ‖y‖ < ‖T y‖ := by
    dsimp [m] at hmargin
    nlinarith
  refine ⟨v, vectorWitness_of_norm_sq_lt d A v ?_⟩
  have hynonneg := norm_nonneg y
  have hTynonneg := norm_nonneg (T y)
  dsimp [T] at hratio ⊢
  nlinarith [sq_nonneg (‖y‖), sq_nonneg (‖T y‖)]

end

end EffectiveMatrixVectorWitnessComplete
end GroupApproximation
