import GroupApproximation.Analysis.CollapseDiscardCoordinates
import GroupApproximation.Meta.AxiomGuard

/-!
# The support corner of a nonunital MF embedding

Let `e : A →⋆ₙₐ Q` be an injective, possibly nonunital, star
homomorphism from a unital C-star algebra to a norm-matrix corona.  Its support
`p = e(1)` is a nonzero projection, every `e(a)` lies in the algebraic corner
`p Q p`, and a projection lift `(P_n)` of `p` is nonzero at infinitely many
coordinates.  Moreover, if `(x_n)` lifts `e(a)`, then `(P_n x_n P_n)` is
another lift of the same element.  These are the exact algebraic and cofinite
parts of unitalization by a support corner.

This file deliberately stops before claiming a unital matrix-corona
embedding.  That final claim requires a bundled star-algebra homomorphism
which simultaneously

* relabels the infinite support of `(P_n)` by a strictly increasing map;
* identifies each finite corner `P_n M_{d_n}(ℂ) P_n` with the full matrix
  algebra on its range; and
* proves that the resulting quotient map is injective on the supported
  corona.

The projection-lifting and finite-corner ingredients exist separately in
`CollapseProjectionLift` and `PrintedCornerCompression`; the missing object is
their exact sequence-level, cofinite-corona assembly.
-/

namespace GroupApproximation
namespace NonUnitalMFSupportCorner

open Filter Matrix Topology

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-- The image of the source unit, which is the unit of the represented
corner. -/
def supportProjection
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) :
    NormMatrixCStarCorona (fun n ↦ Y n) :=
  e 1

/-- The support of a nonunital star homomorphism is self-adjoint. -/
theorem star_supportProjection
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) :
    star (supportProjection Y e) = supportProjection Y e := by
  rw [supportProjection, ← map_star]
  simp

/-- The support of a nonunital star homomorphism is idempotent. -/
theorem supportProjection_mul_self
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) :
    supportProjection Y e * supportProjection Y e = supportProjection Y e := by
  rw [supportProjection, ← map_mul]
  simp

/-- Injectivity prevents the support projection from vanishing. -/
theorem supportProjection_ne_zero
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (he : Function.Injective e) :
    supportProjection Y e ≠ 0 := by
  intro hzero
  have hmap : e (1 : A) = e 0 := by
    simpa [supportProjection] using hzero
  exact one_ne_zero (he hmap)

/-- The support acts as a left identity on the represented algebra. -/
theorem supportProjection_mul_apply
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (a : A) :
    supportProjection Y e * e a = e a := by
  rw [supportProjection, ← map_mul, one_mul]

/-- The support acts as a right identity on the represented algebra. -/
theorem apply_mul_supportProjection
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (a : A) :
    e a * supportProjection Y e = e a := by
  rw [supportProjection, ← map_mul, mul_one]

/-- An injective nonunital corona representation has a projection lift of its
support with infinitely many nonzero coordinates. -/
theorem exists_projection_lift_with_infinite_support
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (he : Function.Injective e) :
    ∃ P : BoundedMatrixSequence (fun n ↦ Y n),
      (∀ n, IsOrthogonalProjectionMatrix (P n)) ∧
        normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e ∧
          {n : ℕ | (P n : Matrix (Y n) (Y n) ℂ) ≠ 0}.Infinite := by
  obtain ⟨P, hP, hPmk⟩ :=
    CollapseProjectionLift.exists_projection_lift Y (supportProjection Y e)
      (star_supportProjection Y e) (supportProjection_mul_self Y e)
  refine ⟨P, hP, hPmk, ?_⟩
  apply CollapseDiscardCoordinates.support_infinite_of_mk_ne_zero Y P
  rw [hPmk]
  exact supportProjection_ne_zero Y e he

/-- Compressing any lift by a projection lift of the support does not change
the represented corona element.  Thus the represented algebra is literally
carried by the coordinate corners before those corners are relabelled and
identified with full matrix algebras. -/
theorem mk_compress_lift_eq
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P x : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (a : A) (hx : normMatrixCStarCoronaMk (fun n ↦ Y n) x = e a) :
    normMatrixCStarCoronaMk (fun n ↦ Y n) (P * x * P) = e a := by
  rw [map_mul, map_mul, hP, hx, supportProjection_mul_apply,
    apply_mul_supportProjection]

#audit_axioms supportProjection_ne_zero
#audit_axioms exists_projection_lift_with_infinite_support
#audit_axioms mk_compress_lift_eq

end

end NonUnitalMFSupportCorner
end GroupApproximation
