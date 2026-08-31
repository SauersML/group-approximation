import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Homogeneous matrix blocks over a real projective space

This file gives a concrete C-star algebra model for the finite blocks in the
STW Problem XXII counterexample.  It avoids a dependency on a vector-bundle
library: a section of the endomorphism bundle of

`1 ⊕ (λ_ℂ)^⊕s → RP^d`

is represented by a continuous matrix-valued function on `S^d` satisfying an
antipodal covariance relation.  Here `λ_ℂ` is the complexification of the
real tautological line bundle.

The construction is first made for any self-adjoint involution `u`.  The
specific diagonal involution used by the counterexample is constructed at the
end of the file.  The fixed-point algebra is proved norm closed and therefore
inherits a C-star algebra structure without any bundle or representation-
theoretic assumption.
-/

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped CStarAlgebra ComplexOrder Matrix

/-- Matrix-valued continuous functions on the sphere.  The fibre has size
`s + 1`, so it is nonempty even when there are no tautological summands. -/
abbrev SphereMatrixFunctions (d s : ℕ) :=
  C(Sphere d, CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)

/-- Antipodal covariance for conjugation by a self-adjoint involution. -/
def IsAntipodalCovariant {d s : ℕ}
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (f : SphereMatrixFunctions d s) : Prop :=
  ∀ x : Sphere d, f (-x) = u * f x * u

/-- The fixed-point star subalgebra of antipodally covariant matrix-valued
functions. -/
def antipodalBlockStarSubalgebra (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    StarSubalgebra ℂ (SphereMatrixFunctions d s) where
  carrier := {f | IsAntipodalCovariant u f}
  zero_mem' := by
    intro x
    simp
  add_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.add_apply, hf x, hg x]
    noncomm_ring
  mul_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.mul_apply, hf x, hg x]
    rw [mul_assoc u (f x) u, ← mul_assoc (u * f x) u u, hu_sq]
    simp [mul_assoc]
  algebraMap_mem' := by
    intro c x
    change algebraMap ℂ (CStarMatrix (Fin k) (Fin k) ℂ) c =
      u * algebraMap ℂ (CStarMatrix (Fin k) (Fin k) ℂ) c * u
    rw [Algebra.commutes c u]
    simp [← mul_assoc, hu_sq]
  star_mem' := by
    intro f hf x
    change star (f (-x)) = u * star (f x) * u
    rw [hf x, star_mul, star_mul, hu_star]
    simp [mul_assoc]

@[simp]
theorem mem_antipodalBlockStarSubalgebra_iff {d s : ℕ}
    {u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ}
    {hu_sq : u * u = 1} {hu_star : star u = u}
    {f : SphereMatrixFunctions d s} :
    f ∈ antipodalBlockStarSubalgebra d s u hu_sq hu_star ↔ IsAntipodalCovariant u f :=
  Iff.rfl

/-- Antipodal covariance is a closed condition in the uniform norm. -/
theorem isClosed_antipodalBlockStarSubalgebra (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    IsClosed ((antipodalBlockStarSubalgebra d s u hu_sq hu_star :
      StarSubalgebra ℂ (SphereMatrixFunctions d s)) : Set (SphereMatrixFunctions d s)) := by
  have hcarrier :
      ((antipodalBlockStarSubalgebra d s u hu_sq hu_star :
        StarSubalgebra ℂ (SphereMatrixFunctions d s)) : Set (SphereMatrixFunctions d s)) =
        ⋂ x : Sphere d, {f | f (-x) = u * f x * u} := by
    ext f
    simp [IsAntipodalCovariant]
  rw [hcarrier]
  refine isClosed_iInter fun x ↦ ?_
  apply isClosed_eq
  · exact continuous_apply (-x)
  · exact (continuous_const.mul (continuous_apply x)).mul continuous_const

/-- The concrete closed C-star algebra of antipodally covariant functions. -/
abbrev AntipodalBlock (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :=
  ↑(antipodalBlockStarSubalgebra d s u hu_sq hu_star)

noncomputable instance antipodalBlock_isClosed (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    IsClosed ((antipodalBlockStarSubalgebra d s u hu_sq hu_star :
      StarSubalgebra ℂ (SphereMatrixFunctions d s)) : Set (SphereMatrixFunctions d s)) :=
  isClosed_antipodalBlockStarSubalgebra d s u hu_sq hu_star

noncomputable instance antipodalBlock_cStarAlgebra (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    CStarAlgebra (AntipodalBlock d s u hu_sq hu_star) :=
  StarSubalgebra.cstarAlgebra _

/-- The sign of a summand: the distinguished trivial line has sign `+1`, and
every tautological summand has sign `-1`. -/
def blockSign {s : ℕ} (i : Fin (s + 1)) : ℂ := if i = 0 then 1 else -1

/-- The diagonal self-adjoint involution implementing the antipodal action on
`1 ⊕ (λ_ℂ)^⊕s`. -/
def blockInvolution (s : ℕ) : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ :=
  CStarMatrix.ofMatrix (Matrix.diagonal blockSign)

@[simp]
theorem blockSign_mul_self {s : ℕ} (i : Fin (s + 1)) : blockSign i * blockSign i = 1 := by
  by_cases hi : i = 0
  · simp [blockSign, hi]
  · simp [blockSign, hi]

@[simp]
theorem blockInvolution_sq (s : ℕ) : blockInvolution s * blockInvolution s = 1 := by
  ext i j
  simp [blockInvolution, CStarMatrix.mul_apply, blockSign]

@[simp]
theorem blockInvolution_star (s : ℕ) : star (blockInvolution s) = blockInvolution s := by
  ext i j
  simp [blockInvolution, CStarMatrix.star_apply, blockSign]

/-- The concrete `s`-th homogeneous block over `RP^d`. -/
abbrev RealProjectiveBlock (d s : ℕ) :=
  AntipodalBlock d s (blockInvolution s) (blockInvolution_sq s)
    (blockInvolution_star s)

end

end STW22
end GroupApproximation
