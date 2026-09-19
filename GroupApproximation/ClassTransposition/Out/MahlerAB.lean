import Mathlib

/-!
# Adamczewski–Bell, Lemma `lem: AB`: rational solutions of a Mahler equation

Adamczewski–Bell (arXiv:1303.2019, *A problem about Mahler functions*, Lemma `lem: AB`, read
at source). Let `K` be a field, `k ≥ 2`, and let `P₀, …, Pₙ ∈ K[X]` with `Pₙ ≠ 0` and
`deg Pₙ ≤ d`. Suppose `F = A / B` is a rational solution of the Mahler equation
`∑ᵢ Pᵢ(X) F(X^{kⁱ}) = 0`, with `A` and `B` coprime. Then `deg B ≤ d`.

The equation for `A / B`, cleared of denominators, is
`∑ᵢ Pᵢ · A(X^{kⁱ}) · ∏_{j ≠ i} B(X^{kʲ}) = 0`. In Mathlib, `F(X^q)` is `expand K q F`.

**Role in Kourovka 17.57.** Let `Φ` be the normalizer sequence. Matui's spatial theorem makes
`Φ mod p` periodic for every `p`, so `Σ Φ(n) Xⁿ mod p` is rational. This lemma bounds its
denominator by the degree `d` of the base-2 Mahler equation, uniformly in `p`. Then the
local–global Lemma `lem: rational` (`Out/LocalGlobal.lean`) makes `Φ` linearly recurrent over
`ℚ`. That route needs no Cobham theorem and no second base.

The proof follows the source. Every term with `i < n` contains the factor `B(X^{kⁿ})`, so
`B(X^{kⁿ})` divides `Pₙ A(X^{kⁿ}) ∏_{j<n} B(X^{kʲ})`. It is coprime to `A(X^{kⁿ})`, so it divides
`Pₙ ∏_{j<n} B(X^{kʲ})`. Comparing degrees, `kⁿ·deg B ≤ d + deg B·(kⁿ - 1)/(k - 1)`.
-/

set_option linter.unusedSimpArgs false

namespace GroupApproximation.ClassTransposition.Out

open Polynomial Finset

theorem geom_sum_lt_pow {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : ∑ j ∈ range n, k ^ j < k ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ]
    have h2 : k ^ n * 2 ≤ k ^ n * k := Nat.mul_le_mul_left (k ^ n) hk
    linarith

theorem erase_range_succ_self (n : ℕ) : (range (n + 1)).erase n = range n := by
  ext j
  simp only [mem_erase, mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    omega
  · intro h
    exact ⟨by omega, by omega⟩

/-- **Adamczewski–Bell, Lemma `lem: AB`.** A rational solution `A / B` (coprime) of a Mahler
equation `∑ᵢ Pᵢ(X) F(X^{kⁱ}) = 0` with `Pₙ ≠ 0` has `deg B ≤ deg Pₙ`. -/
theorem natDegree_denom_le_of_mahler {K : Type*} [Field K] {k n d : ℕ} (hk : 2 ≤ k)
    (P : ℕ → K[X]) (hPn : P n ≠ 0) (hPd : (P n).natDegree ≤ d)
    {A B : K[X]} (hB : B ≠ 0) (hAB : IsCoprime A B)
    (heq : ∑ i ∈ range (n + 1),
      P i * expand K (k ^ i) A * ∏ j ∈ (range (n + 1)).erase i, expand K (k ^ j) B = 0) :
    B.natDegree ≤ d := by
  classical
  have hk0 : ∀ j, 0 < k ^ j := fun j => pow_pos (by omega) j
  have hEB : ∀ j, expand K (k ^ j) B ≠ 0 := fun j =>
    (Polynomial.expand_eq_zero (hk0 j)).not.mpr hB
  rw [sum_range_succ, erase_range_succ_self n] at heq
  -- every lower term is divisible by `B(X^{kⁿ})`
  have hlow : expand K (k ^ n) B ∣ ∑ i ∈ range n,
      P i * expand K (k ^ i) A * ∏ j ∈ (range (n + 1)).erase i, expand K (k ^ j) B := by
    apply Finset.dvd_sum
    intro i hi
    rw [mem_range] at hi
    have hmem : n ∈ (range (n + 1)).erase i := by
      rw [mem_erase, mem_range]
      exact ⟨by omega, by omega⟩
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun j => expand K (k ^ j) B) hmem) _
  have htop : expand K (k ^ n) B ∣
      P n * expand K (k ^ n) A * ∏ j ∈ range n, expand K (k ^ j) B := by
    have e : P n * expand K (k ^ n) A * ∏ j ∈ range n, expand K (k ^ j) B =
        -(∑ i ∈ range n,
          P i * expand K (k ^ i) A * ∏ j ∈ (range (n + 1)).erase i, expand K (k ^ j) B) := by
      linear_combination heq
    rw [e]
    exact (dvd_neg).mpr hlow
  have hcop : IsCoprime (expand K (k ^ n) B) (expand K (k ^ n) A) :=
    hAB.symm.map (expand K (k ^ n)).toRingHom
  have hdiv : expand K (k ^ n) B ∣ P n * ∏ j ∈ range n, expand K (k ^ j) B := by
    apply hcop.dvd_of_dvd_mul_left
    have e : P n * expand K (k ^ n) A * ∏ j ∈ range n, expand K (k ^ j) B =
        expand K (k ^ n) A * (P n * ∏ j ∈ range n, expand K (k ^ j) B) := by ring
    rw [← e]
    exact htop
  have hQ0 : ∏ j ∈ range n, expand K (k ^ j) B ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hEB j
  have hdeg := natDegree_le_of_dvd hdiv (mul_ne_zero hPn hQ0)
  rw [natDegree_expand, natDegree_mul hPn hQ0,
    Polynomial.natDegree_prod (h := fun j _ => hEB j)] at hdeg
  simp only [natDegree_expand] at hdeg
  rw [← Finset.mul_sum] at hdeg
  have hgeom := Nat.lt_iff_add_one_le.mp (geom_sum_lt_pow hk n)
  have h3 := Nat.mul_le_mul_left B.natDegree hgeom
  rw [mul_add, mul_one] at h3
  linarith

end GroupApproximation.ClassTransposition.Out
