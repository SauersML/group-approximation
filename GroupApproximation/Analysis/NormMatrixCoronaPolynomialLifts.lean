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

noncomputable section

universe u

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
  | smul q p hp => simpa using
      congrArg (fun x ↦ RationalHermitian.ofRatPair q • x) hp
  | add p q hp hq => simpa using congrArg₂ (fun x y ↦ x + y) hp hq
  | mul p q hp hq => simpa using congrArg₂ (fun x y ↦ x * y) hp hq
  | star p hp => simpa [lp.star_apply] using congrArg star hp

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
