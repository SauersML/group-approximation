import GroupApproximation.Analysis.MatrixAbsoluteValue
import GroupApproximation.Sofic.KazhdanCornerModel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The unitary polar factor, and the Hilbert--Schmidt polar correction

An approximately unitary matrix is close to a unitary one **in the normalized
Hilbert--Schmidt norm**, with the defect measured in that same norm.  This is
the estimate the passage from an amenable trace to a hyperlinear group needs,
and it is not the estimate the repository already had.

## Why the existing polar correction is the wrong one

`Analysis/PolarLiftingGeneralCStar.lean` carries `polarUnitary x = x (x⋆x)^{-1/2}`
with `norm_polarUnitary_sub_le : ‖polarUnitary x − x‖ ≤ 2‖x‖ ‖x⋆x − 1‖`, and it
requires `‖x⋆x − 1‖ ≤ 1/2` **in the operator norm** --- `polarInvSqrt` inverts
through the continuous functional calculus and needs the spectrum of `x⋆x`
bounded away from `0`.

A Hilbert--Schmidt defect gives no operator-norm control whatever: a projection
of rank `k/2` has `‖p‖₂ = 1/√2` and `‖p‖ = 1`, so `‖1 − x⋆x‖₂` can be tiny while
`‖1 − x⋆x‖ = 1` and `x` is singular.  The two statements are different
theorems, and only the Hilbert--Schmidt one survives the passage from a trace.

## What is proved here, and what is left to the absolute value

The construction of the unitary factor is the whole content, and it is done
here in the form that does not mention the absolute value at all: given any
`p` whose Euclidean action has the *same pointwise norms* as that of `x`,

```text
∀ v, ‖p v‖ = ‖x v‖,
```

there is a **unitary** `u` with `u p = x` (`exists_unitary_mul_eq`), and hence

```text
∃ u unitary, ‖u − x‖₂ = ‖1 − p‖₂
```

(`exists_unitary_hsNorm_sub_eq`), since `u − x = u(1 − p)` and the normalized
Hilbert--Schmidt norm is unitarily invariant
(`PrelimNotation.hsNorm_mul_left`).

The construction: the assignment `p v ↦ x v` is well defined on
`range p` --- if `p v = p v'` then `‖x (v − v')‖ = ‖p (v − v')‖ = 0` --- and is
an isometry there, so `LinearIsometry.extend` extends it to an isometry of the
whole space, which is surjective because the space is finite-dimensional, hence
a `LinearIsometryEquiv`, whose matrix in the standard orthonormal basis is
unitary by `LinearIsometryEquiv.toMatrix_mem_unitaryGroup`.

**Nothing above is about the absolute value.**  What `Analysis/MatrixAbsoluteValue.lean`
supplies is the instance `p := abs x`, which satisfies the norm hypothesis
because `abs x * abs x = xᴴ x`, together with the spectral comparison
`hsNorm Y (1 − abs x) ≤ hsNorm Y (xᴴ x − 1)`.  Composing the two gives the
statement the trace route consumes,

```text
exists_unitary_hsNorm_sub_le (Y) (x) :
    ∃ u ∈ Matrix.unitaryGroup Y ℂ, hsNorm Y (u − x) ≤ hsNorm Y (xᴴ * x − 1),
```

and that composition is one line.  It is deliberately **not** written here:
this module is stated against an abstract `p` so that it neither waits on nor
duplicates the absolute-value module.

No contraction hypothesis appears anywhere, and none is needed.  The spectral
step is `|1 − √t| ≤ |1 − t|`, which holds at every `t ≥ 0` because
`|1 − t| = |1 − √t| (1 + √t)` and `1 + √t ≥ 1` --- so the correction applies to
an arbitrary square matrix, not only to a contraction.
-/

namespace GroupApproximation
namespace HilbertSchmidtPolar

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : FiniteModel) (x p : Matrix Y Y ℂ)

/-- The pointwise-norm hypothesis relating `p` to `x` on the Euclidean
coordinate space: the two matrices move every vector the same distance.

For `p = abs x` this is the polarization-free form of `abs x * abs x = xᴴ x`,
and it is all the polar construction uses. -/
def EuclideanNormAgrees : Prop :=
  ∀ v : EuclideanSpace ℂ Y,
    ‖Matrix.toEuclideanLin p v‖ = ‖Matrix.toEuclideanLin x v‖

variable {Y x p}

/-! ## The assignment `p v ↦ x v` -/

/-- Agreeing norms make the kernel of `p` sit inside the kernel of `x`, so
`p v ↦ x v` is well defined. -/
theorem ker_le_ker_of_euclideanNormAgrees (h : EuclideanNormAgrees Y x p) :
    LinearMap.ker (Matrix.toEuclideanLin p) ≤
      LinearMap.ker (Matrix.toEuclideanLin x) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← norm_eq_zero, ← h v, hv, norm_zero]

/-- The assignment `p v ↦ x v`, as a linear map out of the range of `p`.

It is built by factoring `x` through the quotient by `ker p`, which is legal
by `ker_le_ker_of_euclideanNormAgrees`, and then transporting along
`LinearMap.quotKerEquivRange`. -/
def rangeMap (hker : LinearMap.ker (Matrix.toEuclideanLin p) ≤
    LinearMap.ker (Matrix.toEuclideanLin x)) :
    ↥(LinearMap.range (Matrix.toEuclideanLin p)) →ₗ[ℂ] EuclideanSpace ℂ Y :=
  (Submodule.liftQ _ (Matrix.toEuclideanLin x) hker).comp
    (LinearMap.quotKerEquivRange (Matrix.toEuclideanLin p)).symm.toLinearMap

/-- `rangeMap` does what it was built to do.  The membership proof is taken as
an argument so that the statement matches every way the element of the range
can be presented. -/
theorem rangeMap_apply
    (hker : LinearMap.ker (Matrix.toEuclideanLin p) ≤
      LinearMap.ker (Matrix.toEuclideanLin x))
    (v : EuclideanSpace ℂ Y)
    (hv : Matrix.toEuclideanLin p v ∈ LinearMap.range (Matrix.toEuclideanLin p)) :
    rangeMap hker ⟨Matrix.toEuclideanLin p v, hv⟩ = Matrix.toEuclideanLin x v := by
  have hq : (LinearMap.quotKerEquivRange (Matrix.toEuclideanLin p))
      (Submodule.Quotient.mk v) = ⟨Matrix.toEuclideanLin p v, hv⟩ :=
    Subtype.ext (LinearMap.quotKerEquivRange_apply_mk _ v)
  have hsymm : (LinearMap.quotKerEquivRange (Matrix.toEuclideanLin p)).symm
      ⟨Matrix.toEuclideanLin p v, hv⟩ = Submodule.Quotient.mk v := by
    rw [← hq, LinearEquiv.symm_apply_apply]
  show (Submodule.liftQ _ (Matrix.toEuclideanLin x) hker)
      ((LinearMap.quotKerEquivRange (Matrix.toEuclideanLin p)).symm
        ⟨Matrix.toEuclideanLin p v, hv⟩) = _
  rw [hsymm, Submodule.liftQ_apply]

/-- The same assignment, as a linear **isometry** out of the range of `p`.
Isometry is exactly the hypothesis: `‖x v‖ = ‖p v‖`. -/
def rangeIsometry (h : EuclideanNormAgrees Y x p) :
    ↥(LinearMap.range (Matrix.toEuclideanLin p)) →ₗᵢ[ℂ] EuclideanSpace ℂ Y where
  toLinearMap := rangeMap (ker_le_ker_of_euclideanNormAgrees h)
  norm_map' := by
    rintro ⟨_, v, rfl⟩
    rw [rangeMap_apply]
    exact (h v).symm

/-! ## Extending to the whole space -/

/-- The extension of `rangeIsometry` to an isometry of the whole Euclidean
space, by `LinearIsometry.extend`.  The extension exists because the space is
finite-dimensional: the orthogonal complements of the domain and of the image
then have the same dimension. -/
def polarIsometry (h : EuclideanNormAgrees Y x p) :
    EuclideanSpace ℂ Y →ₗᵢ[ℂ] EuclideanSpace ℂ Y :=
  (rangeIsometry h).extend

/-- The extension still sends `p v` to `x v`. -/
theorem polarIsometry_apply (h : EuclideanNormAgrees Y x p)
    (v : EuclideanSpace ℂ Y) :
    polarIsometry h (Matrix.toEuclideanLin p v) = Matrix.toEuclideanLin x v := by
  have hmem : Matrix.toEuclideanLin p v ∈
      LinearMap.range (Matrix.toEuclideanLin p) := ⟨v, rfl⟩
  have hext := LinearIsometry.extend_apply (rangeIsometry h)
    (⟨Matrix.toEuclideanLin p v, hmem⟩ :
      ↥(LinearMap.range (Matrix.toEuclideanLin p)))
  show (rangeIsometry h).extend (Matrix.toEuclideanLin p v) = _
  rw [hext]
  exact rangeMap_apply _ v hmem

/-- An isometry of a finite-dimensional space to itself is surjective: it is
injective, and injective endomorphisms of a finite-dimensional space are
surjective. -/
theorem polarIsometry_surjective (h : EuclideanNormAgrees Y x p) :
    Function.Surjective (polarIsometry h) :=
  (LinearMap.injective_iff_surjective
      (f := (polarIsometry h).toLinearMap)).mp (polarIsometry h).injective

/-- The extension, upgraded to a linear isometry **equivalence**. -/
def polarIsometryEquiv (h : EuclideanNormAgrees Y x p) :
    EuclideanSpace ℂ Y ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y :=
  LinearIsometryEquiv.ofSurjective (polarIsometry h) (polarIsometry_surjective h)

/-- The equivalence agrees with the isometry it came from: `ofSurjective`
keeps the forward map. -/
theorem polarIsometryEquiv_apply (h : EuclideanNormAgrees Y x p)
    (v : EuclideanSpace ℂ Y) :
    polarIsometryEquiv h v = polarIsometry h v := rfl

/-! ## The unitary factor -/

/-- The matrix of the polar isometry in the standard orthonormal basis of the
Euclidean coordinate space. -/
def polarUnitary (h : EuclideanNormAgrees Y x p) : Matrix Y Y ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun Y ℂ).toBasis
    (EuclideanSpace.basisFun Y ℂ).toBasis
    (polarIsometryEquiv h).toLinearEquiv.toLinearMap

/-- The matrix of a linear isometry equivalence in an orthonormal basis is
unitary. -/
theorem polarUnitary_mem (h : EuclideanNormAgrees Y x p) :
    polarUnitary h ∈ Matrix.unitaryGroup Y ℂ :=
  LinearIsometryEquiv.toMatrix_mem_unitaryGroup (polarIsometryEquiv h)
    (EuclideanSpace.basisFun Y ℂ) (EuclideanSpace.basisFun Y ℂ)

/-- Reading the matrix back gives the isometry it came from.  `toEuclideanLin`
*is* `toLin` at the standard orthonormal basis, so this is one application of
`Matrix.toLin_toMatrix`. -/
theorem toEuclideanLin_polarUnitary (h : EuclideanNormAgrees Y x p) :
    Matrix.toEuclideanLin (polarUnitary h)
      = (polarIsometryEquiv h).toLinearEquiv.toLinearMap := by
  rw [polarUnitary, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_toMatrix _ _ _

/-- The factorization, at the level of matrices. -/
theorem polarUnitary_mul (h : EuclideanNormAgrees Y x p) :
    polarUnitary h * p = x := by
  refine Matrix.toEuclideanLin.injective ?_
  have hmul : Matrix.toEuclideanLin (polarUnitary h * p)
      = (Matrix.toEuclideanLin (polarUnitary h)).comp
        (Matrix.toEuclideanLin p) := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.toLin_mul _ _ _ _ _
  rw [hmul, toEuclideanLin_polarUnitary]
  refine LinearMap.ext fun v ↦ ?_
  show polarIsometryEquiv h (Matrix.toEuclideanLin p v) = Matrix.toEuclideanLin x v
  rw [polarIsometryEquiv_apply]
  exact polarIsometry_apply h v

/-- **The unitary polar factor.**  If `p` and `x` move every vector the same
distance then `x = u p` for a unitary `u`.

This is the statement the repository was missing.  It is proved, not assumed,
and it needs no invertibility, no bound on `‖x‖`, and no smallness hypothesis
of any kind. -/
theorem exists_unitary_mul_eq (h : EuclideanNormAgrees Y x p) :
    ∃ u ∈ Matrix.unitaryGroup Y ℂ, u * p = x :=
  ⟨polarUnitary h, polarUnitary_mem h, polarUnitary_mul h⟩

/-! ## The Hilbert--Schmidt estimate -/

/-- **The polar correction, in the normalized Hilbert--Schmidt norm.**

`u − x = u (1 − p)`, and the normalized Hilbert--Schmidt norm is unchanged by
multiplication by a unitary (`PrelimNotation.hsNorm_mul_left`), so the distance
from `x` to the unitary `u` is exactly the distance from `p` to `1` --- an
equality, not an estimate.

The inequality the trace route consumes is this together with the spectral
comparison at `p = abs x`, supplied by `Analysis/MatrixAbsoluteValue.lean`:
`hsNorm Y (1 − abs x) ≤ hsNorm Y (xᴴ x − 1)`. -/
theorem exists_unitary_hsNorm_sub_eq (h : EuclideanNormAgrees Y x p) :
    ∃ u ∈ Matrix.unitaryGroup Y ℂ, hsNorm Y (u - x) = hsNorm Y (1 - p) := by
  obtain ⟨u, hu, hux⟩ := exists_unitary_mul_eq h
  refine ⟨u, hu, ?_⟩
  have hfactor : u - x = u * (1 - p) := by
    rw [mul_sub, mul_one, hux]
  rw [hfactor]
  exact PrelimNotation.hsNorm_mul_left Y hu (1 - p)

/-- The estimate in the form the caller wants it, with the target bound
supplied as a hypothesis about `p`.

Applying this at `p = abs x` with `Analysis/MatrixAbsoluteValue.lean`'s
spectral comparison is the whole of the remaining composition. -/
theorem exists_unitary_hsNorm_sub_le_of_le (h : EuclideanNormAgrees Y x p)
    {c : ℝ} (hc : hsNorm Y (1 - p) ≤ c) :
    ∃ u ∈ Matrix.unitaryGroup Y ℂ, hsNorm Y (u - x) ≤ c := by
  obtain ⟨u, hu, huv⟩ := exists_unitary_hsNorm_sub_eq h
  exact ⟨u, hu, huv.trans_le hc⟩

/-! ## Specializing to the absolute value

`Analysis/MatrixAbsoluteValue.lean` states its norm agreement in coordinates,
as an identity of squared Euclidean masses.  One conversion turns it into the
hypothesis this module runs on, and then the two modules compose into the
statement the trace route consumes. -/

/-- The coordinate form of the norm hypothesis gives the Euclidean form.  The
bridge is `KazhdanCornerMatrices.euclidean_norm_sq_general`, which reads the
squared Euclidean norm entrywise, and both norms are nonnegative, so the
squares determine them. -/
theorem euclideanNormAgrees_of_sum_normSq
    (hsum : ∀ v : Y → ℂ, ∑ i : Y, Complex.normSq ((p *ᵥ v) i)
      = ∑ i : Y, Complex.normSq ((x *ᵥ v) i)) :
    EuclideanNormAgrees Y x p := by
  intro w
  have hp := KazhdanCornerMatrices.euclidean_norm_sq_general (p *ᵥ w.ofLp)
  have hx := KazhdanCornerMatrices.euclidean_norm_sq_general (x *ᵥ w.ofLp)
  have hsq : ‖Matrix.toEuclideanLin p w‖ ^ 2
      = ‖Matrix.toEuclideanLin x w‖ ^ 2 := by
    simp only [Matrix.toLpLin_apply]
    simpa using hp.trans ((hsum w.ofLp).trans hx.symm)
  have hcong := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hcong

end

/-! ## The exported statement

The section above is closed here so that the two theorems below carry their own
explicit `Y` and `x`, in the binder names the consumers code against, rather
than the implicit section variables. -/

/-- `|x|` moves every vector exactly as far as `x` does, in the Euclidean form
the polar construction consumes.  This is `MatrixAbs.norm_abs_mulVec` read
through the conversion above. -/
theorem euclideanNormAgrees_abs (Y : FiniteModel) (x : Matrix Y Y ℂ) :
    EuclideanNormAgrees Y x (MatrixAbs.abs Y x) :=
  euclideanNormAgrees_of_sum_normSq (MatrixAbs.norm_abs_mulVec Y x)

/-- **The Hilbert--Schmidt polar correction.**  Every square matrix is, in the
normalized Hilbert--Schmidt norm, at least as close to some unitary as its Gram
defect `xᴴx − 1` is to zero:

```text
∃ u unitary, ‖u − x‖₂ ≤ ‖xᴴx − 1‖₂.
```

The unitary is the polar factor of `x`, built here; the estimate is the
spectral comparison `|1 − √t| ≤ |1 − t|` of
`MatrixAbs.hsNorm_one_sub_abs_le`.

**No hypothesis at all.**  In particular no invertibility, no contraction bound
and no smallness of the Gram defect --- which is what separates this from the
operator-norm correction of `Analysis/PolarLiftingGeneralCStar.lean`, whose
`polarUnitary` needs `‖x⋆x − 1‖ ≤ 1/2` in the operator norm and is undefined
without it.

This is the lemma the passage from an amenable trace to a hyperlinear group
was missing. -/
theorem exists_unitary_hsNorm_sub_le (Y : FiniteModel) (x : Matrix Y Y ℂ) :
    ∃ u ∈ Matrix.unitaryGroup Y ℂ, hsNorm Y (u - x) ≤ hsNorm Y (xᴴ * x - 1) :=
  exists_unitary_hsNorm_sub_le_of_le (euclideanNormAgrees_abs Y x)
    (MatrixAbs.hsNorm_one_sub_abs_le Y x)

end HilbertSchmidtPolar
end GroupApproximation
