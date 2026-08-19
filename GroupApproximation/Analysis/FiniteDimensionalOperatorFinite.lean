import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Bounded operators on a finite-dimensional Hilbert space are Dedekind-finite

The manuscript's finite-quotient lemma is stated for an arbitrary sequence of
finite-dimensional Hilbert spaces `K_n`, and forms

`B_c = ∏_n B(K_n) / ⨁_n B(K_n)`.

What the development proves is the same statement with `B(K_n)` replaced by a
matrix algebra over a finite index type (`Sofic/UltraproductDedekindFinite`).
The two agree once a `K_n` is coordinatized by an orthonormal basis, but that
bridge is not a formality about the printed sentence: it is the difference
between "arbitrary finite-dimensional Hilbert space" and "matrices", and until
it is written the printed lemma is broader than the formal one.

This module supplies the coordinate-free half, which is the half that carries
the mathematics: on a finite-dimensional inner product space, an operator with
a left inverse has that same inverse on the right, so an isometry is a unitary
and `B(K)` is Dedekind-finite.  The argument is dimension counting, not
analysis --- `LinearMap.mul_eq_one_comm` --- and it needs no basis, no
coordinates, and no choice of orthonormal frame.

`isUnitary_of_isometry` is the printed adjective ("finite") for one `B(K)`;
`isometry_isUnitary_pi` is the coordinatewise statement over a family, which
is what a product-of-algebras argument consumes before passing to the
quotient.

## Manuscript status

Infrastructure toward the finite-quotient lemma at its printed generality.
Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace FiniteDimensionalOperatorFinite

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [FiniteDimensional ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- A one-sided inverse in `B(K)` is two-sided when `K` is finite-dimensional:
the underlying linear maps compose to the identity, and on a
finite-dimensional space that is a symmetric condition. -/
theorem mul_eq_one_comm {f g : K →L[ℂ] K} (h : f * g = 1) : g * f = 1 := by
  have hlin : (f : K →ₗ[ℂ] K) * (g : K →ₗ[ℂ] K) = 1 := by
    ext x
    exact congrArg (fun T : K →L[ℂ] K ↦ T x) h
  have hcomm : (g : K →ₗ[ℂ] K) * (f : K →ₗ[ℂ] K) = 1 :=
    _root_.mul_eq_one_comm.mp hlin
  ext x
  exact congrArg (fun T : K →ₗ[ℂ] K ↦ T x) hcomm

/-- **`B(K)` is finite** for finite-dimensional `K`: an isometry is a unitary.
This is the printed adjective, coordinate-free. -/
theorem isUnitary_of_isometry {a : K →L[ℂ] K} (h : star a * a = 1) :
    a * star a = 1 :=
  mul_eq_one_comm h

/-- The same statement read coordinatewise over a family of finite-dimensional
Hilbert spaces, which is the form a product-of-algebras argument consumes
before passing to the quotient. -/
theorem isometry_isUnitary_pi {ι : Type*} (K : ι → Type*)
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
    [∀ i, FiniteDimensional ℂ (K i)] [∀ i, CompleteSpace (K i)]
    (a : ∀ i, K i →L[ℂ] K i) (h : ∀ i, star (a i) * a i = 1) (i : ι) :
    a i * star (a i) = 1 :=
  isUnitary_of_isometry (h i)

end

end FiniteDimensionalOperatorFinite
end GroupApproximation
