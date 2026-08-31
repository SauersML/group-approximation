import Mathlib

/-!
# Finite-dimensional factorial trace core for STW Problem XXII

This module kernel-checks the two load-bearing *unconditional* steps in the
finite-dimensional solution of Schafhauser--Tikuisis--White Problem XXII that
do not depend on operator-algebraic or selection-theoretic infrastructure
currently absent from Mathlib:

1. **eventual stable range.**  If a matrix weighted-copy packet has total rank
   `k`, half slack `2*k ≤ n`, and the replication number is at least
   `ceil(j/2)`, then its complementary codimension `n-k` satisfies the sharp
   stable-range inequality `j ≤ 2*(n-k)`;
2. **unbounded replication kills a bounded positive gap trace.**  If a
   nonnegative trace value `x` obeys `m*x ≤ C` for every sufficiently large
   replication number `m`, then `x = 0`.

No axiom, `sorry`, `admit`, or theorem-sized placeholder is introduced here.
The remaining ingredients of the full operator-algebra theorem -- tracially
complete C*-bundles, the weighted-copy fibre topology, and the required
finite-dimensional Michael selection theorem -- are not represented in the
current Lean environment, so this file deliberately does not disguise them as
hypotheses and does not claim a kernel proof of the full XXII statement.
-/

namespace GroupApproximation
namespace FiniteDimensionalFactorialTraceCore

/-- The integer replication threshold `ceil(j / 2)` written without rationals. -/
def replicationThreshold (j : ℕ) : ℕ := (j + 1) / 2

/-- The threshold really puts degree `j` below twice the replication number. -/
theorem degree_le_two_mul_replicationThreshold (j : ℕ) :
    j ≤ 2 * replicationThreshold j := by
  unfold replicationThreshold
  omega

/--
The exact matrix stable-range arithmetic used in the finite-dimensional XXII
argument.  Here `k` is the total replicated support rank and `n-k` is its
complementary codimension.
-/
theorem matrix_stable_range_of_half_slack
    {j m n k : ℕ}
    (hm : replicationThreshold j ≤ m)
    (hmk : m ≤ k)
    (hhalf : 2 * k ≤ n) :
    j ≤ 2 * (n - k) := by
  have hj : j ≤ 2 * replicationThreshold j :=
    degree_le_two_mul_replicationThreshold j
  unfold replicationThreshold at hm hj
  omega

/--
Specialization to `k = m*r`, where `r` is the nonzero support rank of one
weight.  Nonzero rank gives `m ≤ m*r`, so half slack forces the matrix fibre
into the degree-`j` stable range once `m ≥ ceil(j/2)`.
-/
theorem matrix_stable_range_of_nonzero_rank
    {j m n r : ℕ}
    (hr : 0 < r)
    (hm : replicationThreshold j ≤ m)
    (hhalf : 2 * (m * r) ≤ n) :
    j ≤ 2 * (n - m * r) := by
  have hr1 : 1 ≤ r := by omega
  have hmr : m ≤ m * r := by
    calc
      m = m * 1 := by simp
      _ ≤ m * r := Nat.mul_le_mul_left m hr1
  exact matrix_stable_range_of_half_slack hm hmr hhalf

/--
For a base of covering dimension `D`, the proof uses sphere degree `D-1`.
Its eventual replication threshold simplifies to `D/2` in natural-number
arithmetic.
-/
def baseReplicationThreshold (D : ℕ) : ℕ := replicationThreshold (D - 1)

theorem baseReplicationThreshold_eq (D : ℕ) :
    baseReplicationThreshold D = D / 2 := by
  unfold baseReplicationThreshold replicationThreshold
  omega

/--
Archimedean endpoint of the fibre-gap argument: a fixed nonnegative value
cannot stay bounded after multiplication by every sufficiently large natural
number unless it is zero.
-/
theorem nonneg_eq_zero_of_eventual_nat_mul_le
    {x C : ℝ}
    (hx : 0 ≤ x)
    (M : ℕ)
    (hbound : ∀ m : ℕ, M ≤ m → (m : ℝ) * x ≤ C) :
    x = 0 := by
  by_contra hx0
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  obtain ⟨m, hm⟩ := exists_nat_gt (max (M : ℝ) (C / x))
  have hmMreal : (M : ℝ) < (m : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hm
  have hmM : M ≤ m := by
    exact_mod_cast le_of_lt hmMreal
  have hdiv : C / x < (m : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hm
  have hC : C < (m : ℝ) * x :=
    (div_lt_iff₀ hxpos).mp hdiv
  exact (not_lt_of_ge (hbound m hmM)) hC

/--
Function-valued form matching the fibre-gap trace application: if every
positive gap value admits the same eventual replication bound, all of those
values vanish.
-/
theorem bounded_positive_gap_values_vanish
    {α : Type*}
    (σ : α → ℝ)
    (C : ℝ)
    (M : ℕ)
    (hpos : ∀ a, 0 ≤ σ a)
    (hrep : ∀ (a : α) (m : ℕ), M ≤ m → (m : ℝ) * σ a ≤ C) :
    ∀ a, σ a = 0 := by
  intro a
  exact nonneg_eq_zero_of_eventual_nat_mul_le (hpos a) M (hrep a)

/--
A compact statement of the numerical spine used for a finite-dimensional base:
half-slack replication eventually puts every nonzero matrix packet in the
required stable range, while any uniformly bounded positive replicated gap
value vanishes.
-/
theorem finite_dimensional_xxii_numerical_spine
    {D m n r : ℕ}
    {x C : ℝ}
    (hr : 0 < r)
    (hm : baseReplicationThreshold D ≤ m)
    (hhalf : 2 * (m * r) ≤ n)
    (hx : 0 ≤ x)
    (M : ℕ)
    (hbound : ∀ q : ℕ, M ≤ q → (q : ℝ) * x ≤ C) :
    (D - 1 ≤ 2 * (n - m * r)) ∧ x = 0 := by
  constructor
  · apply matrix_stable_range_of_nonzero_rank hr
    · simpa [baseReplicationThreshold] using hm
    · exact hhalf
  · exact nonneg_eq_zero_of_eventual_nat_mul_le hx M hbound

end FiniteDimensionalFactorialTraceCore
end GroupApproximation

-- CI-only branch marker: no semantic change from `main`.
