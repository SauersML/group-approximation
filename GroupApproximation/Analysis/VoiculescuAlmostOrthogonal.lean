import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Almost orthogonal families in a C⋆-ring

Arveson's proof that an approximate unit can be made quasicentral takes convex
combinations of the unit and argues that `0` lies in the *weak* closure of the
convex set of commutator defects, so by Mazur — `Convex.toWeakSpace_closure` at
the pinned revision — in the norm closure.  That argument is unavailable here,
and the obstruction is not the Mazur step but the weak convergence feeding it:
the defects converge to `0` only *strongly*, and upgrading that to convergence
in `σ(K(H), K(H)⋆)` needs the identification of `K(H)⋆` with the trace class,
which the pinned Mathlib does not have (there is no `Schatten`, no
`TraceClass`, and `Analysis/InnerProductSpace/Trace` is the finite-dimensional
trace).  The weak *operator* topology is present, but its continuous dual is
the same as the strong one's, so a convex set's closure in it is the strong
closure and not the norm closure: it cannot stand in.

This module supplies what the trick was for.  The convex combinations Arveson
takes are (in the sequential case) the averages `N⁻¹ ∑ᵢ Gᵢ`, and the reason
their norm is small is that the summands are *almost orthogonal*: the products
`Gᵢ Gⱼ⋆` are small off the diagonal, so the C⋆-identity turns the square of the
norm of the sum into `N` diagonal terms of size `M²` and `N²` off-diagonal
terms of size `δ`, and dividing by `N` leaves `M²/N + δ`.  Nothing here is
about operators: the estimate is stated for a C⋆-ring, since that is all it
uses, and the consumer supplies the smallness by choosing its indices.
-/

namespace GroupApproximation
namespace ShulmanFill

open Finset

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A]

/-- **The almost-orthogonality estimate.**  For a family whose first `N`
members have norm at most `M` and whose off-diagonal products `Gᵢ Gⱼ⋆` have
norm at most `δ`, the square of the norm of the sum is at most `N M² + N² δ`.

The two terms are the diagonal and the off-diagonal of `(∑ Gᵢ)(∑ Gⱼ)⋆`; the
gain over the triangle inequality (which would give `N² M²`) is that only `N`
of the `N²` products are allowed to be of full size. -/
theorem norm_sum_sq_le_of_almostOrthogonal (G : ℕ → A) (N : ℕ) (M δ : ℝ)
    (hδ : 0 ≤ δ) (hdiag : ∀ i < N, ‖G i‖ ≤ M)
    (hoff : ∀ i < N, ∀ j < N, i ≠ j → ‖G i * star (G j)‖ ≤ δ) :
    ‖∑ i ∈ range N, G i‖ ^ 2 ≤ (N : ℝ) * M ^ 2 + (N : ℝ) ^ 2 * δ := by
  have hrow : ∀ i ∈ range N,
      ‖∑ j ∈ range N, G i * star (G j)‖ ≤ (N : ℝ) * δ + M ^ 2 := by
    intro i hi
    have hiN : i < N := mem_range.mp hi
    have hM : 0 ≤ M := (norm_nonneg (G i)).trans (hdiag i hiN)
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ j ∈ range N, ‖G i * star (G j)‖ ≤ δ + if i = j then M ^ 2 else 0 := by
      intro j hj
      by_cases hij : i = j
      · have h1 : ‖G i * star (G i)‖ = ‖G i‖ * ‖G i‖ := CStarRing.norm_self_mul_star
        have h2 : ‖G i‖ * ‖G i‖ ≤ M * M :=
          mul_le_mul (hdiag i hiN) (hdiag i hiN) (norm_nonneg _) hM
        rw [if_pos hij, ← hij, h1]
        linarith
      · rw [if_neg hij]
        have h3 : ‖G i * star (G j)‖ ≤ δ := hoff i hiN j (mem_range.mp hj) hij
        linarith
    calc ∑ j ∈ range N, ‖G i * star (G j)‖
        ≤ ∑ j ∈ range N, (δ + if i = j then M ^ 2 else 0) := sum_le_sum hpt
      _ = (N : ℝ) * δ + M ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
            Finset.sum_ite_eq, if_pos hi]
  have hexp : (∑ i ∈ range N, G i) * star (∑ i ∈ range N, G i)
      = ∑ i ∈ range N, ∑ j ∈ range N, G i * star (G j) := by
    rw [star_sum, Finset.sum_mul_sum]
  calc ‖∑ i ∈ range N, G i‖ ^ 2
      = ‖(∑ i ∈ range N, G i) * star (∑ i ∈ range N, G i)‖ := by
        rw [CStarRing.norm_self_mul_star, pow_two]
    _ = ‖∑ i ∈ range N, ∑ j ∈ range N, G i * star (G j)‖ := by rw [hexp]
    _ ≤ ∑ i ∈ range N, ‖∑ j ∈ range N, G i * star (G j)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range N, ((N : ℝ) * δ + M ^ 2) := sum_le_sum hrow
    _ = (N : ℝ) * ((N : ℝ) * δ + M ^ 2) := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]
    _ = (N : ℝ) * M ^ 2 + (N : ℝ) ^ 2 * δ := by ring

/-- **The estimate in the form the average consumes it.**  Once the two sizes
are small enough that `N M² + N² δ ≤ (N ε)²`, the sum itself has norm at most
`N ε`, so its average over `N` has norm at most `ε`.

The hypothesis is left as the inequality rather than as bounds on `N` and `δ`
separately, because the caller has both numbers in hand and the arithmetic is
one `nlinarith` there. -/
theorem norm_sum_le_of_almostOrthogonal (G : ℕ → A) (N : ℕ) (M δ ε : ℝ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hdiag : ∀ i < N, ‖G i‖ ≤ M)
    (hoff : ∀ i < N, ∀ j < N, i ≠ j → ‖G i * star (G j)‖ ≤ δ)
    (hsize : (N : ℝ) * M ^ 2 + (N : ℝ) ^ 2 * δ ≤ ((N : ℝ) * ε) ^ 2) :
    ‖∑ i ∈ range N, G i‖ ≤ (N : ℝ) * ε :=
  le_of_sq_le_sq ((norm_sum_sq_le_of_almostOrthogonal G N M δ hδ hdiag hoff).trans hsize)
    (mul_nonneg (Nat.cast_nonneg N) hε)

end ShulmanFill
end GroupApproximation
