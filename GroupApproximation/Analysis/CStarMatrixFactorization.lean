import GroupApproximation.Analysis.CStarExactness
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Complete positivity through matrix positivity

Toward proof-ledger row `RE.05` (the Lance debt).  The repository's
`CStarExactness.IsCompletelyPositive` spells complete positivity through
explicit factorizations `M = star N * N`, which is the shape the Stinespring
construction consumes.  The Arveson-extension step of the Lance lane produces
maps whose matrix amplifications are merely *positive* — nonnegative in the
spectral order of `CStarMatrix` — so this file records the equivalence:

* `exists_star_mul_self_of_nonneg` — every positive element of a C⋆-algebra
  is `star N * N`, with `N = CFC.sqrt` of it;
* `isCompletelyPositive_of_map_nonneg` and
  `map_nonneg_of_isCompletelyPositive` — the two directions of
  "completely positive ⟺ positivity-preserving on every matrix level".

Composition of completely positive maps is already
`CStarExactness.IsCompletelyPositive.comp`.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace CStarExactness

universe u v w

/-- **Positive elements factor.**  Every nonnegative element of a
C⋆-algebra is `star N * N`, with `N` its continuous-functional-calculus
square root. -/
theorem exists_star_mul_self_of_nonneg {B : Type u} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] {M : B} (hM : 0 ≤ M) :
    ∃ N : B, M = star N * N := by
  refine ⟨CFC.sqrt M, ?_⟩
  rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)).star_eq,
    CFC.sqrt_mul_sqrt_self M hM]

/-- A linear map whose matrix amplifications preserve positivity is
completely positive in the factorization sense.  The scalar order
hypotheses are the spectral orders that `CStarMatrix`'s own order instance
requires. -/
theorem isCompletelyPositive_of_map_nonneg {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : A →ₗ[ℂ] B)
    (h : ∀ (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) A),
      0 ≤ M → 0 ≤ M.map ⇑φ) :
    IsCompletelyPositive φ := by
  intro n M hM
  obtain ⟨N, rfl⟩ := hM
  exact exists_star_mul_self_of_nonneg (h n _ (star_mul_self_nonneg N))

/-- A completely positive map preserves positivity at every matrix level. -/
theorem map_nonneg_of_isCompletelyPositive {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {φ : A →ₗ[ℂ] B}
    (hφ : IsCompletelyPositive φ) (n : ℕ)
    (M : CStarMatrix (Fin n) (Fin n) A) (hM : 0 ≤ M) :
    0 ≤ M.map ⇑φ := by
  obtain ⟨N, rfl⟩ := exists_star_mul_self_of_nonneg hM
  obtain ⟨P, hP⟩ := hφ n _ ⟨N, rfl⟩
  rw [hP]
  exact star_mul_self_nonneg P

end CStarExactness
end GroupApproximation
