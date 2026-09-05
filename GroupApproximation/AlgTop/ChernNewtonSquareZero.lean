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
this is the algebra that the topological layer will instantiate.

## Main declarations

* `natCast_mul_chern_eq_of_squareZero` — the cleared-denominator form
  `q · c_q = (-1)^{q+1} p_q`, valid in any commutative ring.
* `chern_eq_of_squareZero` — (2.7) itself, `c_q = (-1)^{q+1} (q-1)! ch_q`, over a
  `ℚ`-algebra, where `q` is invertible.
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
square-zero ideal. -/
theorem natCast_mul_chern_eq_of_squareZero (c p : ℕ → A) (hc0 : c 0 = 1)
    (hnewton : ∀ k, 0 < k → (k : A) * c k
      = (-1) ^ (k + 1) *
        ∑ a ∈ Finset.filter (fun a => a.1 < k) (antidiagonal k),
          (-1) ^ a.1 * c a.1 * p a.2)
    (hsq : ∀ i j, 0 < i → 0 < j → c i * p j = 0)
    {k : ℕ} (hk : 0 < k) :
    (k : A) * c k = (-1) ^ (k + 1) * p k := by
  rw [hnewton k hk]
  congr 1
  refine Finset.sum_eq_single (0, k) ?_ ?_
  · rintro ⟨q₁, q₂⟩ hq hne
    rw [Finset.mem_filter, mem_antidiagonal] at hq
    obtain ⟨hsum, hlt⟩ := hq
    simp only at hsum hlt
    have h₁ : 0 < q₁ := by
      rcases Nat.eq_zero_or_pos q₁ with h | h
      · exact absurd (by rw [h]; congr 1; omega : ((q₁, q₂) : ℕ × ℕ) = (0, k)) hne
      · exact h
    have h₂ : 0 < q₂ := by omega
    simp only
    rw [mul_assoc, hsq q₁ q₂ h₁ h₂, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_filter.2 ⟨mem_antidiagonal.2 (by simp), by simpa using hk⟩) hmem

/-- **(2.7).**  Over a `ℚ`-algebra, with `p_q = q! · ch_q`, the square-zero
Newton step gives `c_q = (-1)^{q+1} (q-1)! ch_q`.

Note `(-1)^{q+1} = (-1)^{q-1}`, so this is the manuscript's display verbatim. -/
theorem chern_eq_of_squareZero {A : Type*} [CommRing A] [Algebra ℚ A]
    (c ch : ℕ → A) (hc0 : c 0 = 1)
    (hnewton : ∀ k, 0 < k → (k : A) * c k
      = (-1) ^ (k + 1) *
        ∑ a ∈ Finset.filter (fun a => a.1 < k) (antidiagonal k),
          (-1) ^ a.1 * c a.1 * ((a.2 ! : ℕ) * ch a.2))
    (hsq : ∀ i j, 0 < i → 0 < j → c i * ((j ! : ℕ) * ch j) = 0)
    {k : ℕ} (hk : 0 < k) :
    c k = (-1) ^ (k + 1) * ((k - 1)! : ℕ) * ch k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have key := natCast_mul_chern_eq_of_squareZero c (fun j => ((j ! : ℕ) : A) * ch j)
    hc0 hnewton hsq hk
  have hfac : (((n + 1)! : ℕ) : A) = ((n + 1 : ℕ) : A) * ((n ! : ℕ) : A) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hrewrite : ((n + 1 : ℕ) : A) * c (n + 1)
      = ((n + 1 : ℕ) : A) * ((-1) ^ (n + 1 + 1) * ((n + 1 - 1)! : ℕ) * ch (n + 1)) := by
    rw [key, hfac]
    simp only [Nat.add_sub_cancel]
    ring
  have hu : IsUnit ((n + 1 : ℕ) : A) := by
    have hcast : ((n + 1 : ℕ) : A) = algebraMap ℚ A ((n + 1 : ℕ) : ℚ) := by
      simp
    rw [hcast]
    exact IsUnit.map (algebraMap ℚ A) (isUnit_iff_ne_zero.2 (by positivity))
  exact hu.mul_left_cancel hrewrite

end AlgTop
end GroupApproximation
