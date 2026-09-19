import GroupApproximation.Analysis.CStarIdealQuotient

/-!
# The C⋆-identity on a quotient, from an approximate-unit datum

## What this module proves

`CStarIdealQuotient` made `R ⧸ I` a complete normed ⋆-algebra for a closed
star-stable two-sided ideal `I` of a C⋆-algebra `R`.  What was left of the
standing record's quotient item is the **C⋆-identity** for the quotient norm,
and its classical proof runs through an approximate unit of the ideal.  This
module proves exactly that implication:

* `IdealApproximateUnit I` packages the four norm-level facts the proof
  consumes -- a filter of selfadjoint elements of the ideal along which
  `‖1 - e‖ ≤ 1` and `‖j - j·e‖ → 0` for every `j ∈ I`;
* `quotient_norm_mul_self_le` is the hard half of the C⋆-identity for cosets:
  `‖x‖² ≤ ‖x⋆x‖`, by the textbook computation
  `‖b(1-e)‖² = ‖(1-e)(b⋆b)(1-e)‖ ≤ ‖b⋆b + I‖ + o(1)`;
* `isCStarRing_quotient` assembles `CStarRing (R ⧸ I)` from it.

## Why the datum is a structure and not an instance chase

Mathlib's `CStarAlgebra.increasingApproximateUnit` lives on the ideal viewed
as a C⋆-algebra in its own right, and consuming it there requires the
spectral order on the subtype and a passage of positivity between the
subalgebra and the ambient algebra.  None of that is what the quotient proof
uses: the proof reads only norms in `R`.  Splitting at this exact seam keeps
the analysis here unconditional and order-free, and quarantines the
order-and-subtype work in the module that will *construct* the datum from
Mathlib's filter.  Until that module lands, results here are conditional on
the datum, every statement says so in its binders, and nothing downstream
consumes them.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and
`RE.05` remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarTensor

open Filter

universe u

variable {R : Type u} [CStarAlgebra R] (I : Ideal R) [I.IsTwoSided]
  [IsStarStable I]

/-- **An approximate unit for a two-sided ideal, as norm data.**  The four
facts the quotient C⋆-identity consumes, and nothing else: a nontrivial
filter of selfadjoint elements of the ideal, eventually with `‖1 - e‖ ≤ 1`,
absorbing every element of the ideal from the right in norm.

The canonical construction of such a datum is Mathlib's increasing
approximate unit of the ideal-as-C⋆-algebra; producing it requires spectral
order on the subtype and is deliberately not this module's business. -/
structure IdealApproximateUnit (I : Ideal R) where
  /-- The index filter, living on the ambient algebra. -/
  filter : Filter R
  /-- The filter is nontrivial, so joint eventual properties are realised. -/
  neBot : filter.NeBot
  /-- Eventually the index lies in the ideal. -/
  eventually_mem : ∀ᶠ e in filter, e ∈ I
  /-- Eventually the index is selfadjoint. -/
  eventually_isSelfAdjoint : ∀ᶠ e in filter, IsSelfAdjoint e
  /-- Eventually `‖1 - e‖ ≤ 1`: the approximate unit sits below the unit. -/
  eventually_norm_one_sub : ∀ᶠ e in filter, ‖(1 : R) - e‖ ≤ 1
  /-- The unit absorbs the ideal: `‖j - j·e‖ → 0` for every `j ∈ I`. -/
  tendsto_mul_right : ∀ j ∈ I, Tendsto (fun e => ‖j - j * e‖) filter (nhds 0)

variable {I}

/-- **The hard half of the quotient C⋆-identity**: `‖x‖² ≤ ‖x⋆x‖` for cosets,
given an approximate unit of the ideal.

The computation: for a representative `b` of `x` and an approximate-unit
element `e`, the coset norm is below `‖b(1-e)‖`, whose square is
`‖(1-e)(b⋆b)(1-e)‖` by the C⋆-identity of the ambient algebra; splitting
`b⋆b` into a near-optimal representative `s` of its coset and an ideal
remainder `k`, the first summand is bounded by `‖s‖` and the second is
absorbed by the unit. -/
theorem quotient_norm_mul_self_le (U : IdealApproximateUnit I) (x : R ⧸ I) :
    ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- A near-optimal representative of the coset of `b⋆b`.
  obtain ⟨s, hs_mk, hs⟩ :=
    quotient_norm_mk_lt I (Ideal.Quotient.mk I (star b * b)) (half_pos hδ)
  set k : R := star b * b - s with hkdef
  have hk : k ∈ I := by
    have h0 : Ideal.Quotient.mk I k = 0 := by
      rw [hkdef, map_sub, hs_mk, sub_self]
    rwa [Ideal.Quotient.eq_zero_iff_mem] at h0
  -- One approximate-unit element with every property needed at once.
  haveI := U.neBot
  have hlt : ∀ᶠ y in nhds (0 : ℝ), y < δ / 2 := by
    filter_upwards [Iio_mem_nhds (half_pos hδ)] with y hy
    exact hy
  have hev := ((U.eventually_mem.and U.eventually_isSelfAdjoint).and
    U.eventually_norm_one_sub).and
    ((U.tendsto_mul_right k hk).eventually hlt)
  obtain ⟨e, ⟨⟨hemem, hesa⟩, henorm⟩, hke⟩ := hev.exists
  -- The coset norm is below the corrected norm.
  have h1 : ‖Ideal.Quotient.mk I b‖ ≤ ‖b - b * e‖ := by
    have hbe : b * e ∈ I := I.mul_mem_left b hemem
    have hmk : Ideal.Quotient.mk I (b - b * e) = Ideal.Quotient.mk I b := by
      rw [map_sub, (Ideal.Quotient.eq_zero_iff_mem).mpr hbe, sub_zero]
    rw [← hmk]
    exact quotient_norm_mk_le I _
  -- The C⋆-identity of the ambient algebra on `b(1-e)`.
  have hfact : b - b * e = b * ((1 : R) - e) := by rw [mul_sub, mul_one]
  have hstar : star (b * ((1 : R) - e)) = ((1 : R) - e) * star b := by
    rw [star_mul, star_sub, star_one, hesa.star_eq]
  have h2 : ‖b - b * e‖ * ‖b - b * e‖
      = ‖((1 : R) - e) * (star b * b) * ((1 : R) - e)‖ := by
    have hx := CStarRing.norm_star_mul_self (x := b * ((1 : R) - e))
    rw [hstar] at hx
    rw [hfact, ← hx]
    congr 1
    noncomm_ring
  -- Split along the near-optimal representative.
  have hsplit : ((1 : R) - e) * (star b * b) * ((1 : R) - e)
      = ((1 : R) - e) * s * ((1 : R) - e)
        + ((1 : R) - e) * k * ((1 : R) - e) := by
    rw [hkdef]
    noncomm_ring
  have h3 : ‖((1 : R) - e) * s * ((1 : R) - e)‖ ≤ ‖s‖ := by
    calc ‖((1 : R) - e) * s * ((1 : R) - e)‖
        ≤ ‖((1 : R) - e) * s‖ * ‖(1 : R) - e‖ := norm_mul_le _ _
      _ ≤ ‖(1 : R) - e‖ * ‖s‖ * ‖(1 : R) - e‖ := by
          gcongr
          exact norm_mul_le _ _
      _ ≤ 1 * ‖s‖ * 1 := by gcongr
      _ = ‖s‖ := by ring
  have h4 : ‖((1 : R) - e) * k * ((1 : R) - e)‖ ≤ ‖k - k * e‖ := by
    have hke' : k * ((1 : R) - e) = k - k * e := by rw [mul_sub, mul_one]
    calc ‖((1 : R) - e) * k * ((1 : R) - e)‖
        = ‖((1 : R) - e) * (k * ((1 : R) - e))‖ := by rw [mul_assoc]
      _ ≤ ‖(1 : R) - e‖ * ‖k * ((1 : R) - e)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖k - k * e‖ := by rw [hke']; gcongr
      _ = ‖k - k * e‖ := one_mul _
  -- Assemble.
  have hchain : ‖Ideal.Quotient.mk I b‖ * ‖Ideal.Quotient.mk I b‖
      ≤ ‖s‖ + δ / 2 := by
    calc ‖Ideal.Quotient.mk I b‖ * ‖Ideal.Quotient.mk I b‖
        ≤ ‖b - b * e‖ * ‖b - b * e‖ := by
          exact mul_le_mul h1 h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖((1 : R) - e) * (star b * b) * ((1 : R) - e)‖ := h2
      _ ≤ ‖((1 : R) - e) * s * ((1 : R) - e)‖
          + ‖((1 : R) - e) * k * ((1 : R) - e)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ ‖s‖ + δ / 2 := add_le_add h3 (h4.trans hke.le)
  -- The coset of `b⋆b` is `x⋆x`.
  have hmul : Ideal.Quotient.mk I (star b * b)
      = star (Ideal.Quotient.mk I b) * Ideal.Quotient.mk I b := by
    rw [map_mul, quotient_star_mk]
  calc ‖Ideal.Quotient.mk I b‖ * ‖Ideal.Quotient.mk I b‖
      ≤ ‖s‖ + δ / 2 := hchain
    _ ≤ (‖Ideal.Quotient.mk I (star b * b)‖ + δ / 2) + δ / 2 := by
        linarith [hs]
    _ = ‖star (Ideal.Quotient.mk I b) * Ideal.Quotient.mk I b‖ + δ := by
        rw [hmul]; ring

/-- **The quotient of a C⋆-algebra by a closed star-stable two-sided ideal
with an approximate unit is a C⋆-ring.**  With the normed-ring, ⋆-ring,
normed-algebra and completeness structure already supplied by
`CStarIdealQuotient` and Mathlib, this is the last field of a C⋆-algebra
structure on `R ⧸ I`; the datum is discharged by the module that constructs
the approximate unit from Mathlib's filter on the ideal. -/
theorem isCStarRing_quotient (U : IdealApproximateUnit I)
    [IsClosed (I : Set R)] : CStarRing (R ⧸ I) :=
  { norm_mul_self_le := fun x => quotient_norm_mul_self_le U x }

end CStarTensor
end GroupApproximation
