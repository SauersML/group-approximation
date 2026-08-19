import GroupApproximation.Analysis.CoarseCompression
import GroupApproximation.Kazhdan.GaussianPositiveDefinite

/-!
# Schoenberg's theorem for the Gaussian kernel of an arbitrary map

Guentner--Kaminker's Theorem 3.2 opens with

> Since the function `‖f(s) - f(t)‖²` is of negative type, each `u_k` is
> positive definite by Schoenberg's theorem.

`Kazhdan/GaussianPositiveDefinite.lean` already proves Schoenberg in this
repository, in the shape the Delorme direction of Delorme--Guichardet needs: a
*function on a group* `g ↦ exp(-t‖b g‖²)` attached to a cocycle `b`.  What
Guentner--Kaminker need is the *kernel* shape --- `(s,t) ↦ exp(-κ‖f s - f t‖²)`
for a map `f` with no cocycle identity available --- and this module supplies
it, from exactly the same three ingredients that file already establishes:

* `GaussianKernel.posSemidef_gram` --- Gram matrices are positive semidefinite;
* `GaussianKernel.posSemidef_pow_entry` --- entrywise powers stay positive
  semidefinite (the Schur product theorem, `Matrix.PosSemidef.hadamard`);
* `GaussianKernel.posSemidef_exp_entry` --- hence so do entrywise exponentials.

The factorization is the classical one and needs no group structure:

```
    exp(-κ‖f s - f t‖²)
      = exp(-κ‖f s‖²) · exp(-κ‖f t‖²) · exp⟪√(2κ)·f s, √(2κ)·f t⟫ ,
```

so the quadratic form of the Gaussian kernel at coefficients `c` is the
quadratic form of the entrywise exponential of a Gram matrix at the rescaled
coefficients `c i · exp(-κ‖f (x i)‖²)`.

## What this removes

`Analysis/GuentnerKaminker.lean` carried Schoenberg as a named hypothesis
`hschoenberg`.  It no longer does: `gaussianKernel_isPositiveDefinite` is
unconditional, needing only that the target of `f` is a real inner product
space --- which is what "Hilbert space compression" means in the first place.
-/

namespace GroupApproximation
namespace SchoenbergKernel

open scoped Matrix InnerProductSpace Nat
open CoarseCompression

universe u v

/-- A kernel is **of positive type** if all of its finite real quadratic forms
are nonnegative.  Stated for an arbitrary index type: no algebraic structure on
the source is used, and none is needed. -/
def IsPositiveDefiniteKernel {X : Type*} (u : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, c i * c j * u (x i) (x j)

/-- **The complex form of positive type.**  A real kernel of positive type has
nonnegative complex quadratic forms.  No symmetry is needed: the real and the
imaginary parts of the coefficient vector contribute separately, because
`re (conj c_i · c_j · r) = (Re c_i · Re c_j + Im c_i · Im c_j) · r` for real
`r`, and each of the two resulting sums is a real quadratic form of the same
kernel. -/
theorem IsPositiveDefiniteKernel.complex_re {X : Type*} {u : X → X → ℝ}
    (hu : IsPositiveDefiniteKernel u) (n : ℕ) (x : Fin n → X) (c : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      (starRingEnd ℂ) (c i) * c j * ((u (x i) (x j) : ℝ) : ℂ)).re := by
  have hre : (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ) (c i) * c j * ((u (x i) (x j) : ℝ) : ℂ)).re
      = (∑ i : Fin n, ∑ j : Fin n,
          (c i).re * (c j).re * u (x i) (x j))
        + ∑ i : Fin n, ∑ j : Fin n, (c i).im * (c j).im * u (x i) (x j) := by
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [hre]
  exact add_nonneg (hu n x fun i ↦ (c i).re) (hu n x fun i ↦ (c i).im)

/-- Positive type with the sum indexed by a `Finset` rather than by `Fin n`.
The two are related by `Finset.equivFin`. -/
theorem IsPositiveDefiniteKernel.finset_complex_re {X : Type*} {u : X → X → ℝ}
    (hu : IsPositiveDefiniteKernel u) (F : Finset X) (c : X → ℂ) :
    0 ≤ (∑ i ∈ F, ∑ j ∈ F,
      (starRingEnd ℂ) (c i) * c j * ((u i j : ℝ) : ℂ)).re := by
  classical
  have hone : ∀ ψ : X → ℂ,
      ∑ i ∈ F, ψ i = ∑ i : Fin F.card, ψ ((F.equivFin.symm i : F) : X) := by
    intro ψ
    rw [← Finset.sum_attach F ψ, Finset.attach_eq_univ]
    exact Fintype.sum_equiv F.equivFin _ _ fun x ↦ by rw [Equiv.symm_apply_apply]
  have hre : ∀ kern : X → X → ℂ,
      ∑ i ∈ F, ∑ j ∈ F, kern i j
        = ∑ i : Fin F.card, ∑ j : Fin F.card,
            kern ((F.equivFin.symm i : F) : X) ((F.equivFin.symm j : F) : X) := by
    intro kern
    rw [hone fun i ↦ ∑ j ∈ F, kern i j]
    exact Finset.sum_congr rfl fun i _ ↦ hone _
  rw [hre]
  exact hu.complex_re F.card (fun i ↦ ((F.equivFin.symm i : F) : X)) _

/-- The real quadratic form of a positive semidefinite matrix, written as a
double sum.  This mirrors the private lemma of the same content in
`Kazhdan/GaussianPositiveDefinite.lean`; it is repeated rather than exported
so that the two developments stay independent. -/
private theorem quadForm_nonneg {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * A i j := by
  have hconv : dotProduct (star x) (A.mulVec x) = ∑ i, ∑ j, x i * x j * A i j := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ by ring
  rw [← hconv]
  exact hA.dotProduct_mulVec_nonneg x

variable {G : Type u} [Group G] {E : Type v} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

omit [Group G] in
/-- **Schoenberg's theorem, in kernel form.**  For any map `f` into a real
inner product space and any `κ ≥ 0`, the Gaussian kernel
`u_κ(s,t) = exp(-κ‖f s - f t‖²)` is of positive type.

This is Guentner--Kaminker's first sentence in the proof of Theorem 3.2, and it
is unconditional. -/
theorem gaussianKernel_isPositiveDefinite (f : G → E) {κ : ℝ} (hκ : 0 ≤ κ) :
    IsPositiveDefiniteKernel (gaussianKernel f κ) := by
  classical
  intro n x c
  -- the classical factorization
  have hfact : ∀ i j : Fin n, gaussianKernel f κ (x i) (x j)
      = Real.exp (-(κ * ‖f (x i)‖ ^ 2)) * Real.exp (-(κ * ‖f (x j)‖ ^ 2))
        * Real.exp ⟪Real.sqrt (2 * κ) • f (x i),
            Real.sqrt (2 * κ) • f (x j)⟫_ℝ := by
    intro i j
    rw [gaussianKernel, norm_sub_sq_real, real_inner_smul_left,
      real_inner_smul_right, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [← mul_assoc, Real.mul_self_sqrt (by linarith)]
    ring
  -- the entrywise exponential of a Gram matrix is positive semidefinite
  have hq := quadForm_nonneg
    (GaussianKernel.posSemidef_exp_entry
      (GaussianKernel.posSemidef_gram
        fun i : Fin n ↦ Real.sqrt (2 * κ) • f (x i)))
    (fun i : Fin n ↦ c i * Real.exp (-(κ * ‖f (x i)‖ ^ 2)))
  simp only [Matrix.of_apply] at hq
  refine le_of_le_of_eq hq ?_
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hfact i j]
  ring

end SchoenbergKernel
end GroupApproximation
