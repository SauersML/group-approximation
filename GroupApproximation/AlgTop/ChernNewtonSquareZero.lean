import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Chern classes from the Chern character in the square-zero case

Step (2.6)–(2.7) of the STW Problem LIX manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`).

The manuscript writes

```text
log c(δ) = ∑_{q ≥ 1} (-1)^{q-1} (q-1)! ch_q(δ),
```

observes that all products of terms on the right vanish because they contain
`z² = 0`, and exponentiates to get

```text
c_q(δ) = (-1)^{q-1} (q-1)! ch_q(δ).                              (2.7)
```

This file proves (2.7) **without a logarithm and without an exponential**.  The
relation between the Chern classes `c_q` and the power sums `p_q = q! ch_q` is
Newton's identity

```text
q · c_q = (-1)^{q+1} ∑_{i + j = q, i < q} (-1)^i c_i p_j,
```

and the square-zero hypothesis kills every summand except `i = 0`, which is
`p_q` because `c₀ = 1`.  So the whole of (2.7) is one application of
`Finset.sum_eq_single`.

Both the hypothesis and the conclusion are stated for arbitrary sequences
`c, p : ℕ → A` in a commutative ring, so nothing here is specific to cohomology:
this is the algebra that the topological layer will instantiate.  Newton's
identity itself is discharged for split classes in
`GroupApproximation.AlgTop.TotalChern.newton_of_split`.

## Main declarations

* `natCast_mul_chern_eq_of_squareZero` — the cleared-denominator form
  `q · c_q = (-1)^{q+1} p_q`, valid in any commutative ring.
* `chern_eq_of_squareZero_of_isUnit` — the same with the factor `q` cancelled.
* `isUnit_natCast_of_pos` — `(q : A)` is a unit in a `ℚ`-algebra.
* `chern_eq_of_squareZero` — (2.7) itself, `c_q = (-1)^{q+1} (q-1)! ch_q`, over a
  `ℚ`-algebra.
-/

namespace GroupApproximation
namespace AlgTop

open Finset (antidiagonal mem_antidiagonal)
open scoped Nat

variable {A : Type*} [CommRing A]

/-- **The square-zero Newton step.**  If the Chern classes `c` and the power sums
`p` satisfy Newton's identity, `c₀ = 1`, and every product `c_i p_j` with
`i, j > 0` vanishes, then `q · c_q = (-1)^{q+1} p_q`.

The vanishing hypothesis is what the manuscript gets from `z² = 0`: the virtual
class `δ` has `ch(δ) = z · ch(β)` with `z` of odd total degree squaring to zero,
so all of its positive Chern classes and all of its positive power sums lie in a
square-zero ideal.  See
`GroupApproximation.AlgTop.squareZero_of_dvd_squareZero`. -/
theorem natCast_mul_chern_eq_of_squareZero (c p : ℕ → A) (hc0 : c 0 = 1)
    (hnewton : ∀ k, 0 < k → (k : A) * c k
      = (-1) ^ (k + 1) *
        ∑ a ∈ Finset.filter (fun a : ℕ × ℕ => a.1 < k) (antidiagonal k),
          (-1) ^ a.1 * c a.1 * p a.2)
    (hsq : ∀ i j, 0 < i → 0 < j → c i * p j = 0)
    {k : ℕ} (hk : 0 < k) :
    (k : A) * c k = (-1) ^ (k + 1) * p k := by
  have hmem : ((0, k) : ℕ × ℕ) ∈
      Finset.filter (fun a : ℕ × ℕ => a.1 < k) (antidiagonal k) :=
    Finset.mem_filter.2 ⟨mem_antidiagonal.2 (by simp), by simpa using hk⟩
  have h₀ : ∀ b ∈ Finset.filter (fun a : ℕ × ℕ => a.1 < k) (antidiagonal k),
      b ≠ (0, k) → (-1 : A) ^ b.1 * c b.1 * p b.2 = 0 := by
    rintro ⟨q₁, q₂⟩ hq hne
    rw [Finset.mem_filter, mem_antidiagonal] at hq
    obtain ⟨hsum, hlt⟩ := hq
    simp only at hsum hlt ⊢
    have h₁ : 0 < q₁ := by
      rcases Nat.eq_zero_or_pos q₁ with h | h
      · refine absurd ?_ hne
        simp only [Prod.mk.injEq]
        exact ⟨h, by omega⟩
      · exact h
    rw [mul_assoc, hsq q₁ q₂ h₁ (by omega), mul_zero]
  have h₁ : ((0, k) : ℕ × ℕ) ∉
      Finset.filter (fun a : ℕ × ℕ => a.1 < k) (antidiagonal k) →
      (-1 : A) ^ ((0, k) : ℕ × ℕ).1 * c ((0, k) : ℕ × ℕ).1 * p ((0, k) : ℕ × ℕ).2 = 0 :=
    fun h => absurd hmem h
  rw [hnewton k hk, Finset.sum_eq_single (0, k) h₀ h₁]
  simp [hc0]

/-- (2.7) with the factor `q` cancelled, in any commutative ring in which
`(q : A)` happens to be a unit.  The caller supplies the factorization
`p_q = q · v`; in the intended instance `v = (q-1)! ch_q`. -/
theorem chern_eq_of_squareZero_of_isUnit (c p : ℕ → A) (hc0 : c 0 = 1)
    (hnewton : ∀ k, 0 < k → (k : A) * c k
      = (-1) ^ (k + 1) *
        ∑ a ∈ Finset.filter (fun a : ℕ × ℕ => a.1 < k) (antidiagonal k),
          (-1) ^ a.1 * c a.1 * p a.2)
    (hsq : ∀ i j, 0 < i → 0 < j → c i * p j = 0)
    {k : ℕ} (hk : 0 < k) (hu : IsUnit ((k : ℕ) : A)) (v : A) (hv : p k = (k : A) * v) :
    c k = (-1) ^ (k + 1) * v := by
  refine hu.mul_left_cancel ?_
  rw [natCast_mul_chern_eq_of_squareZero c p hc0 hnewton hsq hk, hv]
  ring

/-- In a `ℚ`-algebra every positive natural number is a unit. -/
theorem isUnit_natCast_of_pos {A : Type*} [CommRing A] [Algebra ℚ A] {k : ℕ} (hk : 0 < k) :
    IsUnit ((k : ℕ) : A) := by
  have hcast : ((k : ℕ) : A) = algebraMap ℚ A ((k : ℕ) : ℚ) := by simp
  rw [hcast]
  refine IsUnit.map (algebraMap ℚ A) (isUnit_iff_ne_zero.2 ?_)
  exact_mod_cast hk.ne'

/-- **(2.7).**  Over a `ℚ`-algebra, with `p_q = q! · ch_q`, the square-zero
Newton step gives `c_q = (-1)^{q+1} (q-1)! ch_q`.

Note `(-1)^{q+1} = (-1)^{q-1}`, so this is the manuscript's display verbatim. -/
theorem chern_eq_of_squareZero {A : Type*} [CommRing A] [Algebra ℚ A]
    (c ch : ℕ → A) (hc0 : c 0 = 1)
    (hnewton : ∀ k, 0 < k → (k : A) * c k
      = (-1) ^ (k + 1) *
        ∑ a ∈ Finset.filter (fun a : ℕ × ℕ => a.1 < k) (antidiagonal k),
          (-1) ^ a.1 * c a.1 * ((a.2 ! : A) * ch a.2))
    (hsq : ∀ i j, 0 < i → 0 < j → c i * ((j ! : A) * ch j) = 0)
    {k : ℕ} (hk : 0 < k) :
    c k = (-1) ^ (k + 1) * (((k - 1)! : A) * ch k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  refine chern_eq_of_squareZero_of_isUnit c (fun j => ((j ! : A)) * ch j) hc0 hnewton hsq hk
    (isUnit_natCast_of_pos hk) _ ?_
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring

end AlgTop
end GroupApproximation
