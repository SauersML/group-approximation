import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.RationalNoncommutativeStarPolynomial

/-!
# Polynomial-compatible lifts from an MF embedding

The reduced-product diagonal proof must choose lifts of the generators, not
independent lifts of every polynomial value.  Functoriality of rational
noncommutative star-polynomial evaluation then makes all polynomial classes
correct simultaneously.  This file packages that step for a single MF
embedding.
-/

namespace GroupApproximation
namespace NormMatrixCoronaPolynomialLifts

open RationalNoncommutativeStarPolynomial
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-- Local assembly of the exact operator-norm matrix C-star parents already
used by the matrix-corona infrastructure. -/
noncomputable local instance matrixBlockCStarAlgebraForPolynomialLifts
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- Local assembly of the exact `lp.inftyRing` C-star parents used by the
matrix-corona quotient map. -/
noncomputable local instance boundedMatrixSequenceCStarAlgebraForPolynomialLifts
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] : CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The public opaque norm-matrix corona has the same limsup norm formula as
its underlying filter quotient. -/
theorem norm_normMatrixCStarCoronaMk_eq_limsup
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    ‖normMatrixCStarCoronaMk (fun n ↦ X n) a‖ =
      Filter.limsup (fun n ↦ ‖a n‖) Filter.cofinite := by
  unfold normMatrixCStarCoronaMk NormMatrixCStarCorona
  exact norm_filterMatrixCorona_mk_eq_limsup (fun n ↦ X n) Filter.cofinite a

/-- Every corona class has a representative within any positive tolerance of
its quotient norm. -/
theorem exists_normMatrixCStarCorona_lift_norm_lt
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (x : NormMatrixCStarCorona (fun n ↦ X n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : BoundedMatrixSequence (fun n ↦ X n),
      normMatrixCStarCoronaMk (fun n ↦ X n) a = x ∧
        ‖a‖ < ‖x‖ + ε := by
  unfold NormMatrixCStarCorona normMatrixCStarCoronaMk
  exact Submodule.Quotient.norm_mk_lt x hε

variable {B : Type u} [CStarAlgebra B]
variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
variable (e : B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
variable (a : ℕ → B)

/-- A chosen near-minimal bounded lift of each embedded generator. -/
def generatorLift (i : ℕ) : BoundedMatrixSequence (fun n ↦ X n) :=
  Classical.choose
    (exists_normMatrixCStarCorona_lift_norm_lt X (e (a i)) (by norm_num : (0 : ℝ) < 1))

theorem generatorLift_quotient (i : ℕ) :
    normMatrixCStarCoronaMk (fun n ↦ X n) (generatorLift X e a i) = e (a i) :=
  (Classical.choose_spec
    (exists_normMatrixCStarCorona_lift_norm_lt X (e (a i))
      (by norm_num : (0 : ℝ) < 1))).1

theorem norm_generatorLift_lt (i : ℕ) :
    ‖generatorLift X e a i‖ < ‖e (a i)‖ + 1 :=
  (Classical.choose_spec
    (exists_normMatrixCStarCorona_lift_norm_lt X (e (a i))
      (by norm_num : (0 : ℝ) < 1))).2

/-- Evaluation of a polynomial in bounded matrix sequences is coordinatewise. -/
theorem eval_generatorLift_apply (p : Polynomial) (n : ℕ) :
    eval (generatorLift X e a) p n =
      eval (fun i ↦ generatorLift X e a i n) p := by
  induction p with
  | zero => rfl
  | generator i => rfl
  | smul q p hp =>
      rw [eval_smul, eval_smul, lp.coeFn_smul, Pi.smul_apply, hp]
  | add p q hp hq =>
      rw [eval_add, eval_add, lp.coeFn_add, Pi.add_apply, hp, hq]
  | mul p q hp hq =>
      rw [eval_mul, eval_mul, lp.infty_coeFn_mul, Pi.mul_apply, hp, hq]
  | star p hp =>
      rw [eval_star, eval_star, lp.coeFn_star, Pi.star_apply, hp]

/-- All rational star polynomials in the chosen generator lifts represent the
embedded polynomial value. -/
theorem polynomialLift_quotient (p : Polynomial) :
    normMatrixCStarCoronaMk (fun n ↦ X n) (eval (generatorLift X e a) p) =
      e (eval a p) := by
  let q := (normMatrixCStarCoronaQuotient (fun n ↦ X n)).toNonUnitalStarAlgHom
  calc
    normMatrixCStarCoronaMk (fun n ↦ X n) (eval (generatorLift X e a) p) =
        eval (fun i ↦ q (generatorLift X e a i)) p :=
      map_eval q (generatorLift X e a) p
    _ = eval (fun i ↦ e (a i)) p := by
      congr 1
      funext i
      exact generatorLift_quotient X e a i
    _ = e (eval a p) := (map_eval e a p).symm

end

end NormMatrixCoronaPolynomialLifts
end GroupApproximation
