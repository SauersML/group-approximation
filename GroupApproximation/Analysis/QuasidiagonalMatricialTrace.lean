import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.CStarChoiMap

/-!
# Tikuisis--White--Winter, unconditionally, for matricially factoring traces

`Analysis.QuasidiagonalTraceProperties` proves the conclusion of
Tikuisis--White--Winter unconditionally in exactly one case: the identity trace
on `ℂ` (`Quasidiagonal.isQuasidiagonalTrace_complex`).  This file proves it
unconditionally for every trace that factors through a matrix algebra:

> if `τ = tr_Y ∘ φ` for a unital `⋆`-homomorphism `φ : A → M_Y`, then `τ` is a
> quasidiagonal trace.

No input, no `KK`-theory, no UCT: the models are the *constant* sequence
`φ, φ, φ, …`, whose multiplicative defect is identically zero and whose
normalized traces are `τ` on the nose.  The one clause that takes work is
complete positivity, and it is proved here from scratch.

## Why this is not vacuous

The class is small --- it is contained in the finite-dimensionally
representable algebras --- but it is strictly larger than `{ℂ}` and it is a
genuine, machine-checkable instance of the theorem's conclusion.  It also
isolates what the theorem is *for*: for a matricially factoring trace,
quasidiagonality is free; the entire content of Tikuisis--White--Winter is
producing models when no such factorization exists, which is why its proof runs
through `KK`-theory and not through any construction of matrix models.

## Complete positivity of a `⋆`-homomorphism into `M_Y`

`Quasidiagonal.IsCompletelyPositiveOnMatrices` is stated as positivity of the
sesquilinear form

  `∑_{i,j} ∑_{x,y} conj(wᵢₓ) · φ(aᵢ⋆aⱼ)ₓᵧ · wⱼᵧ`.

For a `⋆`-homomorphism `φ(aᵢ⋆aⱼ) = φ(aᵢ)⋆φ(aⱼ)`, and the form collapses to
`∑ₜ |Sₜ|²` with `Sₜ = ∑ⱼ ∑ᵧ φ(aⱼ)ₜᵧ wⱼᵧ` --- manifestly real and nonnegative.
`sum_form_star_mul` is that collapse for a single pair of matrices, and it is
the only computational content in the file: expand the entry of `M⋆N`, move the
`t`-summation outermost, and factor the double sum as a product of two sums.
Scalars are complex, hence commutative, so the rearrangements are `ring`.
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ## The form of a product `M⋆N` -/

/-- **The sesquilinear form of `M⋆N` factors.**  This is the matrix identity
behind complete positivity of a `⋆`-homomorphism: the form of `M⋆N` at
`(u, v)` is the ordinary inner product of `Mu` and `Nv`. -/
theorem sum_form_star_mul (Y : FiniteModel) (M N : Matrix Y Y ℂ) (u v : Y → ℂ) :
    (∑ x : Y, ∑ y : Y, (starRingEnd ℂ) (u x) * (star M * N) x y * v y)
      = ∑ t : Y, (starRingEnd ℂ) (∑ x : Y, M t x * u x)
          * (∑ y : Y, N t y * v y) := by
  have hentry : ∀ x y : Y, (star M * N) x y
      = ∑ t : Y, (starRingEnd ℂ) (M t x) * N t y := by
    intro x y
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.star_apply, starRingEnd_apply]
  calc (∑ x : Y, ∑ y : Y, (starRingEnd ℂ) (u x) * (star M * N) x y * v y)
      = ∑ x : Y, ∑ y : Y, ∑ t : Y,
          ((starRingEnd ℂ) (u x) * (starRingEnd ℂ) (M t x))
            * (N t y * v y) := by
        refine Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => ?_
        rw [hentry x y, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
    _ = ∑ x : Y, ∑ t : Y, ∑ y : Y,
          ((starRingEnd ℂ) (u x) * (starRingEnd ℂ) (M t x))
            * (N t y * v y) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ t : Y, ∑ x : Y, ∑ y : Y,
          ((starRingEnd ℂ) (u x) * (starRingEnd ℂ) (M t x))
            * (N t y * v y) := Finset.sum_comm
    _ = ∑ t : Y, (∑ x : Y, (starRingEnd ℂ) (u x) * (starRingEnd ℂ) (M t x))
          * (∑ y : Y, N t y * v y) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_mul_sum]
    _ = ∑ t : Y, (starRingEnd ℂ) (∑ x : Y, M t x * u x)
          * (∑ y : Y, N t y * v y) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        rw [map_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [map_mul]
        ring

/-! ## Complete positivity of a `⋆`-homomorphism -/

/-- **A `⋆`-homomorphism into a matrix algebra is completely positive**, in the
form sense `Quasidiagonal.IsCompletelyPositiveOnMatrices` uses.

The form is `∑ₜ |Sₜ|²`, so its imaginary part vanishes and its real part is a
sum of squared moduli. -/
theorem isCompletelyPositiveOnMatrices_starAlgHom (Y : FiniteModel)
    (φ : A →⋆ₐ[ℂ] Matrix Y Y ℂ) :
    IsCompletelyPositiveOnMatrices Y (fun a : A => φ a) := by
  intro m a w
  set p : Fin m → Y → ℂ := fun i t => ∑ x : Y, φ (a i) t x * w i x with hp
  set S : Y → ℂ := fun t => ∑ j : Fin m, p j t with hS
  have hij : ∀ i j : Fin m,
      (∑ x : Y, ∑ y : Y,
          (starRingEnd ℂ) (w i x) * φ (star (a i) * a j) x y * w j y)
        = ∑ t : Y, (starRingEnd ℂ) (p i t) * p j t := by
    intro i j
    have hmul : φ (star (a i) * a j) = star (φ (a i)) * φ (a j) := by
      rw [map_mul, map_star]
    rw [hmul]
    exact sum_form_star_mul Y (φ (a i)) (φ (a j)) (w i) (w j)
  have hkey : (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
      (starRingEnd ℂ) (w i x) * φ (star (a i) * a j) x y * w j y)
      = ∑ t : Y, (starRingEnd ℂ) (S t) * S t := by
    calc (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
        (starRingEnd ℂ) (w i x) * φ (star (a i) * a j) x y * w j y)
        = ∑ i : Fin m, ∑ j : Fin m, ∑ t : Y,
            (starRingEnd ℂ) (p i t) * p j t :=
          Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => hij i j
      _ = ∑ i : Fin m, ∑ t : Y, ∑ j : Fin m,
            (starRingEnd ℂ) (p i t) * p j t :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ t : Y, ∑ i : Fin m, ∑ j : Fin m,
            (starRingEnd ℂ) (p i t) * p j t := Finset.sum_comm
      _ = ∑ t : Y, (∑ i : Fin m, (starRingEnd ℂ) (p i t))
            * ∑ j : Fin m, p j t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← Finset.sum_mul_sum]
      _ = ∑ t : Y, (starRingEnd ℂ) (S t) * S t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hS]
          congr 1
          rw [map_sum]
  have hnormSq : ∀ t : Y,
      (starRingEnd ℂ) (S t) * S t = ((Complex.normSq (S t) : ℝ) : ℂ) := by
    intro t
    rw [mul_comm, Complex.mul_conj]
  have hreal : (∑ t : Y, (starRingEnd ℂ) (S t) * S t)
      = ((∑ t : Y, Complex.normSq (S t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun t _ => hnormSq t
  constructor
  · rw [hkey, hreal, Complex.ofReal_im]
  · rw [hkey, hreal, Complex.ofReal_re]
    exact Finset.sum_nonneg fun t _ => Complex.normSq_nonneg (S t)

/-! ## The constant model -/

/-- **The constant model** of a matricially factoring trace: the same
`⋆`-homomorphism at every stage.  Its multiplicative defect is identically
zero, and its normalized traces are `τ` exactly. -/
noncomputable def matricialModel (Y : FiniteModel) (φ : A →⋆ₐ[ℂ] Matrix Y Y ℂ) (τ : A → ℂ)
    (hτ : ∀ a : A, τ a = normTrace Y (φ a)) : QuasidiagonalTraceModel τ where
  space _ := Y
  map _ := (φ : A →ₗ[ℂ] Matrix Y Y ℂ)
  map_one _ := by
    show φ 1 = 1
    rw [map_one]
  completelyPositive _ := isCompletelyPositiveOnMatrices_starAlgHom Y φ
  tendsto_mul a b := by
    have h : ∀ _n : ℕ,
        ‖(φ : A →ₗ[ℂ] Matrix Y Y ℂ) (a * b)
          - (φ : A →ₗ[ℂ] Matrix Y Y ℂ) a * (φ : A →ₗ[ℂ] Matrix Y Y ℂ) b‖
          = 0 := by
      intro _n
      have hmul : (φ : A →ₗ[ℂ] Matrix Y Y ℂ) (a * b)
          = (φ : A →ₗ[ℂ] Matrix Y Y ℂ) a * (φ : A →ₗ[ℂ] Matrix Y Y ℂ) b := by
        show φ (a * b) = φ a * φ b
        rw [map_mul]
      rw [hmul, sub_self, norm_zero]
    rw [show (fun n : ℕ =>
        ‖(φ : A →ₗ[ℂ] Matrix Y Y ℂ) (a * b)
          - (φ : A →ₗ[ℂ] Matrix Y Y ℂ) a *
            (φ : A →ₗ[ℂ] Matrix Y Y ℂ) b‖) = (fun _ => 0) from funext h]
    exact tendsto_const_nhds
  tendsto_trace a := by
    have h : ∀ _n : ℕ,
        ‖τ a - normTrace Y ((φ : A →ₗ[ℂ] Matrix Y Y ℂ) a)‖ = 0 := by
      intro _n
      have hval : ((φ : A →ₗ[ℂ] Matrix Y Y ℂ) a) = φ a := rfl
      rw [hval, ← hτ a, sub_self, norm_zero]
    rw [show (fun n : ℕ =>
        ‖τ a - normTrace Y ((φ : A →ₗ[ℂ] Matrix Y Y ℂ) a)‖) =
          (fun _ => 0) from funext h]
    exact tendsto_const_nhds

/-- **Tikuisis--White--Winter's conclusion, unconditionally, for a matricially
factoring trace.**

No hypothesis on `A` beyond the factorization: not separability, not
nuclearity, not the UCT, and not faithfulness of `τ`.  Those hypotheses are
what the theorem needs when no factorization is available; when one is, the
conclusion is immediate. -/
theorem isQuasidiagonalTrace_of_matricial (Y : FiniteModel)
    (φ : A →⋆ₐ[ℂ] Matrix Y Y ℂ) (τ : A → ℂ)
    (hτ : ∀ a : A, τ a = normTrace Y (φ a)) :
    IsQuasidiagonalTrace τ :=
  ⟨matricialModel Y φ τ hτ⟩

end Quasidiagonal
end GroupApproximation
