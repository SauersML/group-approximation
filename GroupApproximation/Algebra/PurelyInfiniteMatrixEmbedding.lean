import GroupApproximation.Algebra.PurelyInfiniteMatrixUnits
import GroupApproximation.Algebra.CornerRing
import Mathlib.Data.Matrix.Basic

/-!
# Embedding `M_n(R)` into `R`, from matrix-unit witnesses

`AGPStepOne`'s ring isomorphism `θ : M_n(R) → PRP` is built here, from raw
matrix-unit witnesses `s, t : Fin n → R` with `t i * s i = 1` and
`t i * s j = 0` (`i ≠ j`) — exactly what `Algebra/PurelyInfiniteMatrixUnits.lean`
constructs from `n` orthogonal copies of `1`.

## The formula

    `θ(A) := ∑ i j, s i * A i j * t j`.

Every property comes from the same single collapse `t i * s j = if i = j then
1 else 0`:

* `θ(1) = ∑ i, s i * t i =: P`, the corner's own unit;
* `θ` lands in the corner `Corner R P hP` because `P * θ(A) = θ(A) = θ(A) * P`
  for every `A`, by the same collapse applied on either side;
* `θ(A * B) = θ(A) * θ(B)`: expanding both sides gives a quadruple sum, and
  the collapse removes exactly the two indices that do not match.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R] {n : ℕ}

section Witnesses

variable (s t : Fin n → R)

/-- The idempotent `P := ∑ i, s i * t i` that `θ`'s image is a corner of. -/
def matrixWitnessSum : R := ∑ i, s i * t i

variable {s t}

theorem isIdempotentElem_matrixWitnessSum (hts : ∀ i, t i * s i = 1)
    (hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0) :
    IsIdempotentElem (matrixWitnessSum s t) := by
  show matrixWitnessSum s t * matrixWitnessSum s t = matrixWitnessSum s t
  have hstep : ∀ i j : Fin n, (s i * t i) * (s j * t j)
      = if i = j then s i * t i else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have h1 : s i * t i * (s i * t i) = s i * (t i * s i) * t i := by
        noncomm_ring
      rw [h1, hts i, mul_one]
    · rw [if_neg hij]
      have h1 : s i * t i * (s j * t j) = s i * (t i * s j) * t j := by
        noncomm_ring
      rw [h1, hcross i j hij, mul_zero, zero_mul]
  calc matrixWitnessSum s t * matrixWitnessSum s t
      = ∑ i, ∑ j, (s i * t i) * (s j * t j) := by
        unfold matrixWitnessSum; rw [Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, (if i = j then s i * t i else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hstep i j
    _ = ∑ i, s i * t i := Finset.sum_congr rfl fun i _ => by
        rw [Finset.sum_eq_single i (fun j _ hji => if_neg (Ne.symm hji))
          (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
    _ = matrixWitnessSum s t := rfl

end Witnesses

/-- **The matrix embedding `θ(A) := ∑ i j, s i * A i j * t j`.** -/
def matrixEmbed (s t : Fin n → R) (A : Matrix (Fin n) (Fin n) R) : R :=
  ∑ i, ∑ j, s i * A i j * t j

variable {s t : Fin n → R}

theorem matrixEmbed_add (A B : Matrix (Fin n) (Fin n) R) :
    matrixEmbed s t (A + B) = matrixEmbed s t A + matrixEmbed s t B := by
  unfold matrixEmbed
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show s i * (A + B) i j * t j = s i * A i j * t j + s i * B i j * t j
  show s i * (A i j + B i j) * t j = _
  rw [mul_add, add_mul]

theorem matrixEmbed_one :
    matrixEmbed s t (1 : Matrix (Fin n) (Fin n) R) = matrixWitnessSum s t := by
  unfold matrixEmbed matrixWitnessSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by
      show s i * (1 : Matrix (Fin n) (Fin n) R) i j * t j = 0
      rw [Matrix.one_apply_ne (Ne.symm hji), mul_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h)]
  show s i * (1 : Matrix (Fin n) (Fin n) R) i i * t i = s i * t i
  rw [Matrix.one_apply_eq, mul_one]

theorem matrixEmbed_mem_corner (hts : ∀ i, t i * s i = 1)
    (hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0)
    (A : Matrix (Fin n) (Fin n) R) :
    matrixWitnessSum s t * matrixEmbed s t A = matrixEmbed s t A ∧
      matrixEmbed s t A * matrixWitnessSum s t = matrixEmbed s t A := by
  constructor
  · have hstep : ∀ k i j : Fin n, s k * t k * (s i * A i j * t j)
        = if k = i then s k * A i j * t j else 0 := by
      intro k i j
      by_cases hki : k = i
      · subst hki
        rw [if_pos rfl]
        have h1 : s k * t k * (s k * A k j * t j)
            = s k * (t k * s k) * A k j * t j := by noncomm_ring
        rw [h1, hts k, mul_one]
      · rw [if_neg hki]
        have h1 : s k * t k * (s i * A i j * t j)
            = s k * (t k * s i) * A i j * t j := by noncomm_ring
        rw [h1, hcross k i hki]
        simp
    unfold matrixWitnessSum matrixEmbed
    calc (∑ k, s k * t k) * ∑ i, ∑ j, s i * A i j * t j
        = ∑ k, ∑ i, ∑ j, s k * t k * (s i * A i j * t j) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by
              rw [Finset.mul_sum]
      _ = ∑ k, ∑ i, ∑ j, (if k = i then s k * A i j * t j else 0) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => hstep k i j
      _ = ∑ k, ∑ j, s k * A k j * t j :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.sum_eq_single k
              (fun i _ hik =>
                (Finset.sum_congr rfl fun j _ => if_neg (fun h => hik h.symm)).trans
                  Finset.sum_const_zero)
              (fun h => absurd (Finset.mem_univ k) h)]
            exact Finset.sum_congr rfl fun j _ => by rw [if_pos rfl]
      _ = ∑ i, ∑ j, s i * A i j * t j := rfl
  · unfold matrixWitnessSum matrixEmbed
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    show (s i * A i j * t j) * ∑ k, s k * t k = s i * A i j * t j
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single j (fun k _ hkj => ?_)
      (fun h => absurd (Finset.mem_univ j) h)]
    · have h1 : (s i * A i j * t j) * (s j * t j)
          = s i * A i j * (t j * s j) * t j := by noncomm_ring
      rw [h1, hts j, mul_one]
    · have h1 : (s i * A i j * t j) * (s k * t k)
          = s i * A i j * (t j * s k) * t k := by noncomm_ring
      rw [h1, hcross j k (Ne.symm hkj), mul_zero, zero_mul]

/-- **`θ` is multiplicative.**  Expanding both sides gives a quadruple sum;
the collapse `t j * s k = if j = k then 1 else 0` removes the mismatched
indices, leaving exactly `Matrix.mul`'s own defining sum. -/
theorem matrixEmbed_mul (hts : ∀ i, t i * s i = 1)
    (hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0)
    (A B : Matrix (Fin n) (Fin n) R) :
    matrixEmbed s t (A * B) = matrixEmbed s t A * matrixEmbed s t B := by
  have hstep : ∀ i j k l : Fin n, (s i * A i j * t j) * (s k * B k l * t l)
      = if j = k then s i * (A i j * B k l) * t l else 0 := by
    intro i j k l
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      have h1 : (s i * A i j * t j) * (s j * B j l * t l)
          = s i * A i j * (t j * s j) * B j l * t l := by noncomm_ring
      rw [h1, hts j]
      have h2 : s i * A i j * 1 * B j l * t l = s i * (A i j * B j l) * t l := by
        noncomm_ring
      rw [h2]
    · rw [if_neg hjk]
      have h1 : (s i * A i j * t j) * (s k * B k l * t l)
          = s i * A i j * (t j * s k) * B k l * t l := by noncomm_ring
      rw [h1, hcross j k hjk]
      simp
  unfold matrixEmbed
  refine Eq.symm ?_
  calc (∑ i, ∑ j, s i * A i j * t j) * ∑ k, ∑ l, s k * B k l * t l
      = ∑ i, ∑ j, ∑ k, ∑ l, (s i * A i j * t j) * (s k * B k l * t l) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (if j = k then s i * (A i j * B k l) * t l else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
            hstep i j k l
    _ = ∑ i, ∑ j, ∑ l, s i * (A i j * B j l) * t l := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single j
          (fun k _ hkj =>
            (Finset.sum_congr rfl fun l _ => if_neg (Ne.symm hkj)).trans
              Finset.sum_const_zero)
          (fun h => absurd (Finset.mem_univ j) h)]
        exact Finset.sum_congr rfl fun l _ => by rw [if_pos rfl]
    _ = ∑ i, ∑ l, s i * (A * B) i l * t l := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    _ = matrixEmbed s t (A * B) := rfl

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.isIdempotentElem_matrixWitnessSum
#audit_axioms GroupApproximation.MFQuotientUnits.matrixEmbed_add
#audit_axioms GroupApproximation.MFQuotientUnits.matrixEmbed_one
#audit_axioms GroupApproximation.MFQuotientUnits.matrixEmbed_mem_corner
#audit_axioms GroupApproximation.MFQuotientUnits.matrixEmbed_mul
