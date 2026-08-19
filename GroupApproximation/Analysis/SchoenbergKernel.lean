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
