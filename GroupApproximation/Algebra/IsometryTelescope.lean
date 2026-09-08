import GroupApproximation.Algebra.PurelyInfiniteSandwich

/-!
# The telescope of a one-sided inverse

A single one-sided inverse pair `t * s = 1` splits the unit into as many
orthogonal, pairwise **equivalent** idempotents as one likes, plus a remainder
equivalent to `1`:

    `1 = g₀ + g₁ + ⋯ + g_{m-1} + sᵐ tᵐ`,   `gₖ = sᵏ (1 - s t) tᵏ`

with the `gₖ` pairwise orthogonal, every `gₖ` equivalent to `g₀ = 1 - s t`, and
`sᵐ tᵐ` equivalent to `1`.  Nothing here needs the ring to be simple or purely
infinite; the telescope is a consequence of `t * s = 1` alone.

## Why this, and not absorption

Ara--Goodearl--Pardo Theorem 2.4 (a) asks for orthogonal `e₁, …, e_m` summing to
`1` with `e₁, …, e_{m-1}` **pairwise equivalent** and `e_m` equivalent to an
idempotent `f ≤ e₁`.  It is tempting to read that as asking for pieces
equivalent to `1` — which is what a matrix decomposition `R ≅ M_m(R)` would
need, and what a Schröder--Bernstein or "absorption" theorem would be for.

Both readings are wrong, and in the same way.  `R ≅ M_m(R)` forces
`(m-1)·[1] = 0` in `K₀`, which fails for purely infinite simple rings with `[1]`
of infinite order; and Schröder--Bernstein for idempotents is false in a purely
infinite simple ring for a sharper reason — comparability makes *every* pair of
nonzero idempotents mutually sub-equivalent, so the hypothesis is vacuous and
the conclusion would say all nonzero idempotents are equivalent.

The printed statement asks only that the first `m-1` pieces be equivalent **to
each other**, with the last **sub**-equivalent to the first.  The telescope
below delivers exactly that, because the `gₖ` are all equivalent to `g₀` rather
than to `1`.  Equivalence to `g`, not to `1`, is what is free.
-/

namespace GroupApproximation
namespace MFQuotientUnits

section Telescope

variable {R : Type*} [Ring R] {s t : R}

/-- The complementary idempotent of a one-sided inverse pair. -/
def isoComplement (s t : R) : R := 1 - s * t

theorem isoComplement_mul_left (hts : t * s = 1) :
    isoComplement s t * s = 0 := by
  show (1 - s * t) * s = 0
  have h1 : (1 - s * t) * s = s - s * (t * s) := by noncomm_ring
  rw [h1, hts, mul_one, sub_self]

theorem mul_isoComplement_right (hts : t * s = 1) :
    t * isoComplement s t = 0 := by
  show t * (1 - s * t) = 0
  have h1 : t * (1 - s * t) = t - (t * s) * t := by noncomm_ring
  rw [h1, hts, one_mul, sub_self]

theorem isIdempotentElem_isoComplement (hts : t * s = 1) :
    IsIdempotentElem (isoComplement s t) := by
  show (1 - s * t) * (1 - s * t) = 1 - s * t
  have h1 : (1 - s * t) * (1 - s * t)
      = 1 - s * t - s * t + s * (t * s) * t := by noncomm_ring
  rw [h1, hts, mul_one]
  noncomm_ring

/-- `tᵏ sᵏ = 1` for every `k`. -/
theorem pow_mul_pow_eq_one (hts : t * s = 1) : ∀ k : ℕ, t ^ k * s ^ k = 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : t ^ (k + 1) = t ^ k * t := pow_succ t k
      have h2 : s ^ (k + 1) = s * s ^ k := pow_succ' s k
      rw [h1, h2, mul_assoc, ← mul_assoc t s, hts, one_mul]
      exact ih

/-! ### The pieces -/

/-- The `k`-th piece of the telescope. -/
def telescopePiece (s t : R) (k : ℕ) : R := s ^ k * isoComplement s t * t ^ k

theorem isIdempotentElem_telescopePiece (hts : t * s = 1) (k : ℕ) :
    IsIdempotentElem (telescopePiece s t k) := by
  show telescopePiece s t k * telescopePiece s t k = telescopePiece s t k
  have hg := isIdempotentElem_isoComplement hts
  calc telescopePiece s t k * telescopePiece s t k
      = s ^ k * isoComplement s t * (t ^ k * s ^ k) *
          isoComplement s t * t ^ k := by
        unfold telescopePiece; noncomm_ring
    _ = s ^ k * (isoComplement s t * isoComplement s t) * t ^ k := by
        rw [pow_mul_pow_eq_one hts]; noncomm_ring
    _ = telescopePiece s t k := by rw [hg]; rfl

/-- Each piece is equivalent to the complementary idempotent, via the explicit
pair `(sᵏ g, g tᵏ)`. -/
theorem isEquivalentIdempotent_telescopePiece (hts : t * s = 1) (k : ℕ) :
    IsEquivalentIdempotent R (telescopePiece s t k) (isoComplement s t) := by
  have hg := isIdempotentElem_isoComplement hts
  refine ⟨s ^ k * isoComplement s t, isoComplement s t * t ^ k, ?_, ?_⟩
  · show s ^ k * isoComplement s t * t ^ k
      = s ^ k * isoComplement s t * (isoComplement s t * t ^ k)
    have h1 : s ^ k * isoComplement s t * (isoComplement s t * t ^ k)
        = s ^ k * (isoComplement s t * isoComplement s t) * t ^ k := by
      noncomm_ring
    rw [h1, hg]
  · have h1 : isoComplement s t * t ^ k * (s ^ k * isoComplement s t)
        = isoComplement s t * (t ^ k * s ^ k) * isoComplement s t := by
      noncomm_ring
    rw [h1, pow_mul_pow_eq_one hts, mul_one, hg]

/-- Distinct pieces are orthogonal. -/
theorem telescopePiece_mul_of_ne (hts : t * s = 1) {k l : ℕ} (hkl : k ≠ l) :
    telescopePiece s t k * telescopePiece s t l = 0 := by
  have hgs : ∀ n : ℕ, isoComplement s t * s ^ (n + 1) = 0 := by
    intro n
    rw [pow_succ' s, ← mul_assoc, isoComplement_mul_left hts, zero_mul]
  have htg : ∀ n : ℕ, t ^ (n + 1) * isoComplement s t = 0 := by
    intro n
    rw [pow_succ, mul_assoc, mul_isoComplement_right hts, mul_zero]
  show s ^ k * isoComplement s t * t ^ k *
    (s ^ l * isoComplement s t * t ^ l) = 0
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · obtain ⟨n, hn⟩ : ∃ n, l - k = n + 1 := ⟨l - k - 1, by omega⟩
    have hsplit : s ^ l = s ^ k * s ^ (l - k) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    have h1 : s ^ k * isoComplement s t * t ^ k *
        (s ^ k * s ^ (l - k) * isoComplement s t * t ^ l)
        = s ^ k * isoComplement s t * (t ^ k * s ^ k) *
          (s ^ (l - k) * isoComplement s t * t ^ l) := by noncomm_ring
    rw [h1, pow_mul_pow_eq_one hts]
    have h2 : s ^ k * isoComplement s t * 1 *
        (s ^ (l - k) * isoComplement s t * t ^ l)
        = s ^ k * (isoComplement s t * s ^ (l - k)) *
          (isoComplement s t * t ^ l) := by noncomm_ring
    rw [h2, hn, hgs n, mul_zero, zero_mul]
  · obtain ⟨n, hn⟩ : ∃ n, k - l = n + 1 := ⟨k - l - 1, by omega⟩
    have hsplit : t ^ k = t ^ (k - l) * t ^ l := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    have h1 : s ^ k * isoComplement s t * (t ^ (k - l) * t ^ l) *
        (s ^ l * isoComplement s t * t ^ l)
        = s ^ k * isoComplement s t * t ^ (k - l) * (t ^ l * s ^ l) *
          (isoComplement s t * t ^ l) := by noncomm_ring
    rw [h1, pow_mul_pow_eq_one hts]
    have h2 : s ^ k * isoComplement s t * t ^ (k - l) * 1 *
        (isoComplement s t * t ^ l)
        = s ^ k * isoComplement s t *
          (t ^ (k - l) * isoComplement s t) * t ^ l := by noncomm_ring
    rw [h2, hn, htg n, mul_zero, zero_mul]

/-! ### The telescope -/

/-- **The telescope.**  `1` splits into `m` orthogonal pieces, each equivalent
to `1 - s t`, plus a remainder `sᵐ tᵐ`. -/
theorem telescope_sum : ∀ m : ℕ,
    (∑ k ∈ Finset.range m, telescopePiece s t k) + s ^ m * t ^ m = 1 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : telescopePiece s t m + s ^ (m + 1) * t ^ (m + 1)
          = s ^ m * t ^ m := by
        have h1 : telescopePiece s t m
            = s ^ m * t ^ m - s ^ (m + 1) * t ^ (m + 1) := by
          unfold telescopePiece isoComplement
          rw [pow_succ s, pow_succ' t]
          noncomm_ring
        rw [h1]
        abel
      rw [Finset.sum_range_succ]
      calc (∑ k ∈ Finset.range m, telescopePiece s t k) +
            telescopePiece s t m + s ^ (m + 1) * t ^ (m + 1)
          = (∑ k ∈ Finset.range m, telescopePiece s t k) +
              (telescopePiece s t m + s ^ (m + 1) * t ^ (m + 1)) := by abel
        _ = (∑ k ∈ Finset.range m, telescopePiece s t k) + s ^ m * t ^ m := by
            rw [hstep]
        _ = 1 := ih

/-- The remainder is an idempotent equivalent to `1`. -/
theorem isEquivalentIdempotent_remainder (hts : t * s = 1) (m : ℕ) :
    IsIdempotentElem (s ^ m * t ^ m) ∧
      IsEquivalentIdempotent R (s ^ m * t ^ m) 1 := by
  constructor
  · show s ^ m * t ^ m * (s ^ m * t ^ m) = s ^ m * t ^ m
    calc s ^ m * t ^ m * (s ^ m * t ^ m)
        = s ^ m * (t ^ m * s ^ m) * t ^ m := by noncomm_ring
      _ = s ^ m * t ^ m := by rw [pow_mul_pow_eq_one hts]; noncomm_ring
  · exact ⟨s ^ m, t ^ m, rfl, (pow_mul_pow_eq_one hts m).symm⟩

end Telescope

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.pow_mul_pow_eq_one
#audit_axioms GroupApproximation.MFQuotientUnits.isEquivalentIdempotent_telescopePiece
#audit_axioms GroupApproximation.MFQuotientUnits.telescopePiece_mul_of_ne
#audit_axioms GroupApproximation.MFQuotientUnits.telescope_sum
#audit_axioms GroupApproximation.MFQuotientUnits.isEquivalentIdempotent_remainder
