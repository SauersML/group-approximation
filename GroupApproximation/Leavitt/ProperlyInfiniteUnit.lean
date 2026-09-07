import GroupApproximation.Leavitt.OneSidedInverse

/-!
# Properly infinite units, and the reformulation of the printed hypothesis

`notes/rank-two-descent-note-2026-09-07.md`, §1.

The printed hypothesis of `thm:full-defect-ring` is a one-sided inverse pair
`ts = 1` together with fullness of the complementary idempotent `e = 1 - st`:
finitely many `a_j, b_j` with `∑_j a_j e b_j = 1`.  The note observes that this
package is equivalent to a single, symmetric piece of data:

> two sections `v₀, v₁` and two retractions `w₀, w₁` with `wᵢvⱼ = δᵢⱼ`.

No relation `v₀w₀ + v₁w₁ = 1` is asked for, so this is *properly infinite*
rather than a decomposition of the unit; the name follows the operator-algebra
usage.

## The two directions

Fullness gives the pair by the note's explicit formulas: with `m` the number of
fullness witnesses,

`v₀ = sᵐ`,  `w₀ = tᵐ`,  `v₁ = ∑_j sʲ e bⱼ`,  `w₁ = ∑_j aⱼ e tʲ`.

The whole calculation rests on one identity, `e tⁱ sʲ e = δᵢⱼ e`, which holds for *all*
naturals `i, j` and not only for `i, j < m`: for `j > i` the middle collapses to
a positive power of `s`, which `e` kills on the left, and for `i > j` to a
positive power of `t`, which `e` kills on the right.

Conversely a properly infinite unit gives back the printed hypothesis with a
*single* witness: `s = v₀`, `t = w₀`, and `w₁(1 - v₀w₀)v₁ = 1`.  So the
descent may be run from either form, and `PrintedProperlyInfiniteReformulation`
records that they are the same hypothesis.
-/

namespace GroupApproximation
namespace RankDescent

open OneSidedCompressor

variable {R : Type*} [Ring R]

/-! ## Powers of a one-sided inverse pair -/

/-- `tⁱsⁱ = 1`, the only consequence of `ts = 1` the descent needs. -/
theorem t_pow_mul_s_pow_self (P : OneSidedInverse R) (i : ℕ) :
    P.t ^ i * P.s ^ i = 1 := by
  induction i with
  | zero => simp
  | succ n ih =>
      have ht : P.t ^ (n + 1) = P.t ^ n * P.t := by rw [pow_add, pow_one]
      have hs : P.s ^ (n + 1) = P.s * P.s ^ n := by
        rw [add_comm, pow_add, pow_one]
      rw [ht, hs]
      calc P.t ^ n * P.t * (P.s * P.s ^ n)
          = P.t ^ n * (P.t * P.s) * P.s ^ n := by noncomm_ring
        _ = P.t ^ n * P.s ^ n := by rw [P.t_mul_s, mul_one]
        _ = 1 := ih

/-- More retractions than sections leaves a power of the section. -/
theorem t_pow_mul_s_pow_of_le (P : OneSidedInverse R) {i j : ℕ} (h : i ≤ j) :
    P.t ^ i * P.s ^ j = P.s ^ (j - i) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  rw [pow_add, ← mul_assoc, t_pow_mul_s_pow_self, one_mul,
    Nat.add_sub_cancel_left]

/-- More sections than retractions leaves a power of the retraction. -/
theorem t_pow_mul_s_pow_of_ge (P : OneSidedInverse R) {i j : ℕ} (h : j ≤ i) :
    P.t ^ i * P.s ^ j = P.t ^ (i - j) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + j := ⟨i - j, by omega⟩
  rw [pow_add, mul_assoc, t_pow_mul_s_pow_self, mul_one, Nat.add_sub_cancel]

/-- **The orthogonality identity of §1.**  `e tⁱ sʲ e = δᵢⱼ e`, for all
naturals `i` and `j`. -/
theorem e_mul_t_pow_mul_s_pow_mul_e (P : OneSidedInverse R) (i j : ℕ) :
    P.e * P.t ^ i * P.s ^ j * P.e = if i = j then P.e else 0 := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · rw [if_neg (by omega : ¬ i = j)]
    obtain ⟨d, hd⟩ : ∃ d, j - i = d + 1 := ⟨j - i - 1, by omega⟩
    have h := t_pow_mul_s_pow_of_le P (le_of_lt hlt)
    calc P.e * P.t ^ i * P.s ^ j * P.e
        = P.e * (P.t ^ i * P.s ^ j) * P.e := by noncomm_ring
      _ = P.e * P.s ^ (j - i) * P.e := by rw [h]
      _ = P.e * P.s ^ (d + 1) * P.e := by rw [hd]
      _ = 0 := by rw [P.e_mul_s_pow, zero_mul]
  · rw [if_pos heq]
    subst heq
    calc P.e * P.t ^ i * P.s ^ i * P.e
        = P.e * (P.t ^ i * P.s ^ i) * P.e := by noncomm_ring
      _ = P.e * P.e := by rw [t_pow_mul_s_pow_self, mul_one]
      _ = P.e := P.e_mul_e
  · rw [if_neg (by omega : ¬ i = j)]
    obtain ⟨d, hd⟩ : ∃ d, i - j = d + 1 := ⟨i - j - 1, by omega⟩
    have h := t_pow_mul_s_pow_of_ge P (le_of_lt hgt)
    calc P.e * P.t ^ i * P.s ^ j * P.e
        = P.e * (P.t ^ i * P.s ^ j) * P.e := by noncomm_ring
      _ = P.e * (P.t ^ (i - j) * P.e) := by rw [h]; noncomm_ring
      _ = P.e * (P.t ^ (d + 1) * P.e) := by rw [hd]
      _ = 0 := by rw [P.t_pow_mul_e, mul_zero]

/-! ## Properly infinite units -/

/-- **A properly infinite unit.**  Two sections and two retractions with
`wᵢvⱼ = δᵢⱼ`.  Nothing is asked about `v₀w₀ + v₁w₁`. -/
structure ProperlyInfiniteUnit (R : Type*) [Ring R] where
  /-- The two sections. -/
  v : Fin 2 → R
  /-- The two retractions. -/
  w : Fin 2 → R
  /-- The defining relations `wᵢvⱼ = δᵢⱼ`. -/
  w_mul_v : ∀ i j, w i * v j = if i = j then 1 else 0

namespace ProperlyInfiniteUnit

variable (Q : ProperlyInfiniteUnit R)

theorem w_mul_v_self (i : Fin 2) : Q.w i * Q.v i = 1 := by
  simpa using Q.w_mul_v i i

theorem w_mul_v_of_ne {i j : Fin 2} (h : i ≠ j) : Q.w i * Q.v j = 0 := by
  simpa [h] using Q.w_mul_v i j

/-! ### A properly infinite unit is a full one-sided inverse pair -/

/-- The zeroth section and retraction form a one-sided inverse pair. -/
def toOneSidedInverse : OneSidedInverse R where
  s := Q.v 0
  t := Q.w 0
  t_mul_s := Q.w_mul_v_self 0

@[simp] theorem toOneSidedInverse_s : Q.toOneSidedInverse.s = Q.v 0 := rfl

@[simp] theorem toOneSidedInverse_t : Q.toOneSidedInverse.t = Q.w 0 := rfl

theorem toOneSidedInverse_e : Q.toOneSidedInverse.e = 1 - Q.v 0 * Q.w 0 := rfl

/-- **The single fullness witness of §1**: `w₁(1 - v₀w₀)v₁ = 1`.  The first
index pair is orthogonal to the second, which is all that is used. -/
theorem w_one_mul_e_mul_v_one :
    Q.w 1 * Q.toOneSidedInverse.e * Q.v 1 = 1 := by
  have h10 : Q.w 1 * Q.v 0 = 0 := Q.w_mul_v_of_ne (by decide)
  have h11 : Q.w 1 * Q.v 1 = 1 := Q.w_mul_v_self 1
  rw [toOneSidedInverse_e]
  calc Q.w 1 * (1 - Q.v 0 * Q.w 0) * Q.v 1
      = Q.w 1 * Q.v 1 - Q.w 1 * Q.v 0 * (Q.w 0 * Q.v 1) := by noncomm_ring
    _ = 1 := by rw [h10, h11, zero_mul, sub_zero]

/-- The complementary idempotent of `toOneSidedInverse` is full, with one
witness. -/
theorem toOneSidedInverse_isFull :
    ∃ (m : ℕ) (a b : Fin m → R),
      ∑ k, a k * Q.toOneSidedInverse.e * b k = 1 :=
  ⟨1, fun _ ↦ Q.w 1, fun _ ↦ Q.v 1, by simpa using Q.w_one_mul_e_mul_v_one⟩

end ProperlyInfiniteUnit

/-! ## From fullness to a properly infinite unit -/

section OfFull

variable (P : OneSidedInverse R) {m : ℕ} (a b : Fin m → R)

/-- `w₀v₀ = tᵐsᵐ = 1`. -/
theorem full_w0_mul_v0 : P.t ^ m * P.s ^ m = 1 :=
  t_pow_mul_s_pow_self P m

/-- `w₀v₁ = ∑ⱼ t^{m-j} e bⱼ = 0`: each exponent `m - j` is positive. -/
theorem full_w0_mul_v1 :
    P.t ^ m * (∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k) = 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hk : (k : ℕ) ≤ m := le_of_lt k.isLt
  obtain ⟨d, hd⟩ : ∃ d, m - (k : ℕ) = d + 1 := ⟨m - (k : ℕ) - 1, by omega⟩
  have h := t_pow_mul_s_pow_of_ge P hk
  calc P.t ^ m * (P.s ^ (k : ℕ) * P.e * b k)
      = P.t ^ m * P.s ^ (k : ℕ) * P.e * b k := by noncomm_ring
    _ = P.t ^ (m - (k : ℕ)) * P.e * b k := by rw [h]
    _ = P.t ^ (d + 1) * P.e * b k := by rw [hd]
    _ = 0 := by rw [P.t_pow_mul_e, zero_mul]

/-- `w₁v₀ = ∑ⱼ aⱼ e s^{m-j} = 0`: each exponent `m - j` is positive. -/
theorem full_w1_mul_v0 :
    (∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)) * P.s ^ m = 0 := by
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hk : (k : ℕ) ≤ m := le_of_lt k.isLt
  obtain ⟨d, hd⟩ : ∃ d, m - (k : ℕ) = d + 1 := ⟨m - (k : ℕ) - 1, by omega⟩
  have h := t_pow_mul_s_pow_of_le P hk
  calc a k * P.e * P.t ^ (k : ℕ) * P.s ^ m
      = a k * (P.e * (P.t ^ (k : ℕ) * P.s ^ m)) := by noncomm_ring
    _ = a k * (P.e * P.s ^ (m - (k : ℕ))) := by rw [h]
    _ = a k * (P.e * P.s ^ (d + 1)) := by rw [hd]
    _ = 0 := by rw [P.e_mul_s_pow, mul_zero]

/-- `w₁v₁ = ∑ⱼ aⱼ e bⱼ = 1`: the orthogonality identity collapses the double
sum to its diagonal, which is the fullness witness. -/
theorem full_w1_mul_v1 (hab : ∑ k, a k * P.e * b k = 1) :
    (∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)) *
        (∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k) = 1 := by
  rw [Finset.sum_mul_sum]
  have key : ∀ i j : Fin m,
      (a i * P.e * P.t ^ (i : ℕ)) * (P.s ^ (j : ℕ) * P.e * b j)
        = if i = j then a i * P.e * b i else 0 := by
    intro i j
    have h := e_mul_t_pow_mul_s_pow_mul_e P (i : ℕ) (j : ℕ)
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl] at h ⊢
      calc a i * P.e * P.t ^ (i : ℕ) * (P.s ^ (i : ℕ) * P.e * b i)
          = a i * (P.e * P.t ^ (i : ℕ) * P.s ^ (i : ℕ) * P.e) * b i := by
            noncomm_ring
        _ = a i * P.e * b i := by rw [h]
    · have hne : ¬ ((i : ℕ) = (j : ℕ)) := fun hc ↦ hij (Fin.ext hc)
      rw [if_neg hne] at h
      rw [if_neg hij]
      calc a i * P.e * P.t ^ (i : ℕ) * (P.s ^ (j : ℕ) * P.e * b j)
          = a i * (P.e * P.t ^ (i : ℕ) * P.s ^ (j : ℕ) * P.e) * b j := by
            noncomm_ring
        _ = 0 := by rw [h]; noncomm_ring
  simp only [key]
  simpa using hab

/-- **§1 of the note.**  A one-sided inverse pair whose complementary
idempotent is full carries a properly infinite unit. -/
def ofFull (hab : ∑ k, a k * P.e * b k = 1) : ProperlyInfiniteUnit R where
  v := ![P.s ^ m, ∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k]
  w := ![P.t ^ m, ∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)]
  w_mul_v := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using full_w0_mul_v0 P (m := m)
    · simpa using full_w0_mul_v1 P b
    · simpa using full_w1_mul_v0 P a
    · simpa using full_w1_mul_v1 P a b hab

end OfFull

/-! ## The two hypotheses are the same hypothesis -/

/-- **The reformulation of §1, as one closed proposition.**  For every unital
ring, a full one-sided inverse pair and a properly infinite unit are
interchangeable data.

The note states the equivalence for nonzero `R`; it in fact needs no such
hypothesis, because in the zero ring both sides hold vacuously. -/
def PrintedProperlyInfiniteReformulation : Prop :=
  ∀ (R : Type) [Ring R],
    (∃ (P : OneSidedInverse R) (m : ℕ) (a b : Fin m → R),
        ∑ k, a k * P.e * b k = 1) ↔ Nonempty (ProperlyInfiniteUnit R)

theorem manuscriptProperlyInfiniteReformulation :
    PrintedProperlyInfiniteReformulation := by
  intro R _
  constructor
  · rintro ⟨P, m, a, b, hab⟩
    exact ⟨ofFull P a b hab⟩
  · rintro ⟨Q⟩
    obtain ⟨m, a, b, hab⟩ := Q.toOneSidedInverse_isFull
    exact ⟨Q.toOneSidedInverse, m, a, b, hab⟩

end RankDescent
end GroupApproximation
