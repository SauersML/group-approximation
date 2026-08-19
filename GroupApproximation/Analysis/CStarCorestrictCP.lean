import GroupApproximation.Analysis.CStarMatrixFactorization

/-!
# Complete positivity corestricts to a subalgebra

`IsNuclearMap` asks for its second factor to land in the algebra being
approximated.  The Lance approximation produces a map into the *ambient*
`B(ℓ²)` together with a proof that its values lie in the reduced algebra.
Corestricting the map is `LinearMap.codRestrict`; corestricting the *predicate*
is what this file does, and it is not formal — `IsCompletelyPositive` asks for a
factorization `star P * P`, and the factorization one is handed is built over
the ambient algebra, with no reason for `P` to have entries in the subalgebra.

## What makes it true, isolated

`CStarMatrixFactorization` already replaces the factorization by an order
condition in both directions: a map is completely positive exactly when every
matrix amplification of it preserves positivity.  Read through that equivalence,
corestriction stops being about factorizations at all.  The corestricted map
preserves positivity as soon as the ambient one does **and positivity comes back
along the inclusion** --- if the amplified image is positive in the ambient
matrix algebra, it was positive upstairs.

That reflection is the entire content, and it is a statement about the
inclusion, not about the map being corestricted.  It is true because positivity
in a C⋆-algebra is spectral and a `⋆`-monomorphism of C⋆-algebras is isometric,
so the spectrum does not move; equivalently, the square root produced by the
continuous functional calculus stays inside a closed `⋆`-subalgebra, which is
Mathlib's `cfc_mem` and is the same step `Analysis/RoeSquareRoot` runs for the
Roe algebra.

So `isCompletelyPositive_codRestrict` takes the reflection as a hypothesis
stated in ordinary order vocabulary at the inclusion, and everything else about
corestriction is discharged here.  The hypothesis is a fact to be proved about
the reduced algebra's inclusion, not a citation: nothing in the literature is
being imported, and the statement mentions no theorem of anyone's.
-/

namespace GroupApproximation
namespace CStarExactness

universe u v

/-- **Complete positivity corestricts along a positivity-reflecting map.**

`ι` is the inclusion of the target subalgebra, `ψ` the corestriction, and the
two are related by `ι ∘ ψ = φ`.  The reflection hypothesis says exactly that
`ι`'s matrix amplifications detect positivity rather than merely preserve it.

Read through `CStarMatrixFactorization`, no factorization has to be transported:
positivity of `M.map φ` is positivity of `(M.map ψ).map ι`, and reflection puts
it upstairs. -/
theorem isCompletelyPositive_codRestrict
    {A : Type u} {B C : Type v}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    {φ : A →ₗ[ℂ] B} {ψ : A →ₗ[ℂ] C} {ι : C →ₗ[ℂ] B}
    (hfactor : ∀ a : A, ι (ψ a) = φ a)
    (hreflect : ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) C),
      0 ≤ X.map ⇑ι → 0 ≤ X)
    (hφ : IsCompletelyPositive φ) :
    IsCompletelyPositive ψ := by
  refine isCompletelyPositive_of_map_nonneg ψ ?_
  intro n M hM
  refine hreflect n (M.map ⇑ψ) ?_
  have hcomp : (M.map ⇑ψ).map ⇑ι = M.map ⇑φ := by
    ext i j
    exact hfactor (M i j)
  rw [hcomp]
  exact map_nonneg_of_isCompletelyPositive hφ n M hM

/-- The reflection hypothesis is not vacuous: the identity reflects. -/
theorem reflect_id {C : Type v}
    [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) C)
    (h : 0 ≤ X.map ⇑(LinearMap.id : C →ₗ[ℂ] C)) : 0 ≤ X := by
  have hmap : X.map ⇑(LinearMap.id : C →ₗ[ℂ] C) = X := by
    ext i j
    rfl
  rwa [hmap] at h

end CStarExactness
end GroupApproximation
