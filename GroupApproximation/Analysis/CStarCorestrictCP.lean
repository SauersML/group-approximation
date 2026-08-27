import GroupApproximation.Analysis.CStarMatrixFactorization
import GroupApproximation.Analysis.LanceMatrixSubalgebra

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
corestriction is discharged here.

And for the case the Lance lane actually needs, the reflection is **not** a
hypothesis: `exists_factor_entries_mem_of_isCompletelyPositive` discharges it
outright from `LanceMatrixSubalgebra.exists_entries_mem_factor`, which was
already proved.  Stated that way it needs no corestriction and no instance
assembly on the subalgebra --- the entries are constrained by membership rather
than by type, so everything stays in the ambient algebra.
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

/-- **The factorization can be taken inside the subalgebra.**  This is the
concrete form of the reflection, and it discharges the difficulty outright for
the case that matters: a completely positive map whose values lie in a *closed*
`⋆`-subalgebra factors its amplifications through matrices over that subalgebra.

No corestriction, no instance assembly on the subalgebra: everything is stated
in the ambient algebra, and the entries are constrained by membership rather
than by type.  `LanceMatrixSubalgebra.exists_entries_mem_factor` is what does
the work --- the square root taken inside the C⋆-algebra the closed entrywise
subalgebra carries, whose spectra agree with the ambient ones by spectral
permanence --- and this is the sentence the Lance approximation needs it in. -/
theorem exists_factor_entries_mem_of_isCompletelyPositive
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (C : StarSubalgebra ℂ B) (hC : IsClosed (C : Set B))
    {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyPositive φ) (hval : ∀ a : A, φ a ∈ C)
    (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) A)
    (hM : ∃ N : CStarMatrix (Fin n) (Fin n) A, M = star N * N) :
    ∃ P : CStarMatrix (Fin n) (Fin n) B,
      (∀ p q, P p q ∈ C) ∧ M.map ⇑φ = star P * P := by
  have hMpos : 0 ≤ M := by
    obtain ⟨N, rfl⟩ := hM
    exact star_mul_self_nonneg N
  have hpos : 0 ≤ M.map ⇑φ :=
    map_nonneg_of_isCompletelyPositive hφ n M hMpos
  exact exists_entries_mem_factor C hC (fun p q ↦ hval (M p q)) hpos

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
