import GroupApproximation.Analysis.VoiculescuAlmostOrthogonal
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Analysis.Real.Sqrt

/-!
# The `√n` estimate for sums against orthogonal projections

`Analysis/VoiculescuAlmostOrthogonal` proves, for a C⋆-ring,

    ‖∑_{i<N} Gᵢ‖² ≤ N M² + N² δ   when ‖Gᵢ‖ ≤ M and ‖Gᵢ G_j⋆‖ ≤ δ for i ≠ j.

At `δ = 0` — the exactly orthogonal case — this reads `‖∑ Gᵢ‖ ≤ √N · M`, and
that is the form Powers' averaging argument consumes.  This module supplies it,
indexed by `Fin n` rather than by `Finset.range N`, and in the two shapes the
argument produces:

* `norm_sum_mul_projection_le` — `‖∑ᵢ Aᵢ Qᵢ‖ ≤ √n · M`;
* `norm_sum_projection_mul_le` — `‖∑ᵢ Qᵢ Bᵢ‖ ≤ √n · M`.

Both take the `Qᵢ` to be self-adjoint with `Qᵢ Q_j = 0` for `i ≠ j` and
`‖Qᵢ‖ ≤ 1`; no idempotence is used.  The second follows from the first by
applying `star`, which turns `∑ Qᵢ Bᵢ` into `∑ (Bᵢ)⋆ Qᵢ` and preserves norms.

## Where the orthogonality comes from

In Powers' argument the `Qᵢ` are the coordinate projections `P_{gᵢ D}` of
`ℓ²(G)` onto the translates of one set `D` by the averaging elements, and the
hypothesis `Qᵢ Q_j = 0` is exactly the disjointness of those translates
(`Analysis/GroupHilbertSubsetProjection.subsetProjection_mul_of_disjoint`).

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace ShulmanFill

open Finset

universe u

variable {A : Type u} [NonUnitalNormedRing A] [StarRing A] [CStarRing A]

/-! ## The exactly orthogonal case, indexed by `Fin n` -/

/-- **The orthogonal estimate.**  A family whose members have norm at most `M`
and whose off-diagonal products `Fᵢ F_j⋆` vanish has
`‖∑ᵢ Fᵢ‖² ≤ n M²`.

This is `norm_sum_sq_le_of_almostOrthogonal` at off-diagonal size `δ = 0`,
transported from `Finset.range n` to `Fin n` by extending the family by zero. -/
theorem norm_sum_sq_le_of_orthogonal {n : ℕ} (F : Fin n → A) (M : ℝ)
    (hdiag : ∀ i, ‖F i‖ ≤ M) (hoff : ∀ i j, i ≠ j → F i * star (F j) = 0) :
    ‖∑ i, F i‖ ^ 2 ≤ (n : ℝ) * M ^ 2 := by
  classical
  set F' : ℕ → A := fun k ↦ if h : k < n then F ⟨k, h⟩ else 0 with hF'
  have hF'apply : ∀ (k : ℕ) (h : k < n), F' k = F ⟨k, h⟩ := fun _ h ↦ dif_pos h
  have hsum : ∑ i, F i = ∑ k ∈ range n, F' k := by
    rw [← Fin.sum_univ_eq_sum_range F' n]
    exact Finset.sum_congr rfl fun i _ ↦ (hF'apply i.1 i.isLt).symm
  have hdiag' : ∀ k < n, ‖F' k‖ ≤ M := by
    intro k hk
    rw [hF'apply k hk]
    exact hdiag _
  have hoff' : ∀ k < n, ∀ l < n, k ≠ l → ‖F' k * star (F' l)‖ ≤ 0 := by
    intro k hk l hl hkl
    rw [hF'apply k hk, hF'apply l hl,
      hoff ⟨k, hk⟩ ⟨l, hl⟩ (fun hcon ↦ hkl (congrArg Fin.val hcon)), norm_zero]
  have hbound := norm_sum_sq_le_of_almostOrthogonal F' n M 0 le_rfl hdiag' hoff'
  rw [← hsum] at hbound
  simpa using hbound

/-! ## The two shapes Powers' argument produces -/

/-- **`‖∑ᵢ Aᵢ Qᵢ‖ ≤ √n · M`** for pairwise orthogonal self-adjoint `Qᵢ` of norm
at most one and `‖Aᵢ‖ ≤ M`. -/
theorem norm_sum_mul_projection_le {n : ℕ} (a q : Fin n → A) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ i, ‖a i‖ ≤ M) (hq : ∀ i, ‖q i‖ ≤ 1) (hqstar : ∀ i, star (q i) = q i)
    (hqorth : ∀ i j, i ≠ j → q i * q j = 0) :
    ‖∑ i, a i * q i‖ ≤ Real.sqrt n * M := by
  have hdiag : ∀ i, ‖a i * q i‖ ≤ M := by
    intro i
    calc ‖a i * q i‖ ≤ ‖a i‖ * ‖q i‖ := norm_mul_le _ _
      _ ≤ M * 1 := by
          exact mul_le_mul (ha i) (hq i) (norm_nonneg _) hM
      _ = M := mul_one M
  have hoff : ∀ i j, i ≠ j → (a i * q i) * star (a j * q j) = 0 := by
    intro i j hij
    rw [star_mul, hqstar j, ← mul_assoc, mul_assoc (a i) (q i) (q j),
      hqorth i j hij, mul_zero, zero_mul]
  have hsq := norm_sum_sq_le_of_orthogonal (fun i ↦ a i * q i) M hdiag hoff
  have hnn : (0 : ℝ) ≤ Real.sqrt n * M := mul_nonneg (Real.sqrt_nonneg _) hM
  have hkey : ‖∑ i, a i * q i‖ * ‖∑ i, a i * q i‖
      ≤ (Real.sqrt n * M) * (Real.sqrt n * M) := by
    have hexp : (Real.sqrt n * M) * (Real.sqrt n * M)
        = (Real.sqrt n * Real.sqrt n) * (M * M) := by ring
    rw [hexp, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    calc ‖∑ i, a i * q i‖ * ‖∑ i, a i * q i‖ = ‖∑ i, a i * q i‖ ^ 2 := (sq _).symm
      _ ≤ (n : ℝ) * M ^ 2 := hsq
      _ = (n : ℝ) * (M * M) := by rw [sq]
  have := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_mul_self (norm_nonneg _), Real.sqrt_mul_self hnn] at this

/-- **`‖∑ᵢ Qᵢ Bᵢ‖ ≤ √n · M`**, the mirror form.  Applying `star` turns the sum
into `∑ᵢ (Bᵢ)⋆ Qᵢ`, which the previous theorem bounds. -/
theorem norm_sum_projection_mul_le {n : ℕ} (b q : Fin n → A) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i, ‖b i‖ ≤ M) (hq : ∀ i, ‖q i‖ ≤ 1) (hqstar : ∀ i, star (q i) = q i)
    (hqorth : ∀ i j, i ≠ j → q i * q j = 0) :
    ‖∑ i, q i * b i‖ ≤ Real.sqrt n * M := by
  have hstar : star (∑ i, q i * b i) = ∑ i, star (b i) * q i := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [star_mul, hqstar i]
  have hnorm : ‖∑ i, q i * b i‖ = ‖∑ i, star (b i) * q i‖ := by
    rw [← hstar, norm_star]
  rw [hnorm]
  exact norm_sum_mul_projection_le (fun i ↦ star (b i)) q M hM
    (fun i ↦ by rw [norm_star]; exact hb i) hq hqstar hqorth

end ShulmanFill
end GroupApproximation

open GroupApproximation.ShulmanFill

#audit_axioms norm_sum_sq_le_of_orthogonal
#audit_axioms norm_sum_mul_projection_le
#audit_axioms norm_sum_projection_mul_le
