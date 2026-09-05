import GroupApproximation.AlgTop.ChernPowerSums

/-!
# `hlow` of Lemma 3, without K-theory

Lane `lix-obstruction`, campaign target 3 (STW Problem LIX).

`AlgTop/MappingTorusParity.lean` proves Lemma 3 from five hypotheses and charges

```text
hlow : ∀ q, 0 < q → q < 3 → (W / V).powerSum q = 0
```

to `found-ktheory-bott`, via the manuscript's route: the split restriction sequence
and the free-case Künneth give
`ker(K⁰(S¹ × M) → K⁰(M)) = K¹(S¹) ⊗ K¹(S⁵) ⊗ K⁰(Y)`, so `ch(δ) = z · ch(β)` with
`z = t x` of degree six, and the low Chern-character components vanish for degree
reasons.

**That is more than `hlow` needs.**  `hlow` follows from the vanishing of the two low
*Chern classes* of `δ`, by Newton's identity alone — no Chern character, no `K`-theory,
no Künneth.  That is `powerSum_eq_zero_of_lt_three` below, and it is pure algebra in
`TotalChern A`.

And the two low Chern classes vanish for a reason much cheaper than the Künneth
decomposition.  With `N = S¹ × M` and `M = S⁵ × Y`, the `S¹`-Künneth splitting is just
`H^n(N) = H^n(M) ⊕ t · H^{n-1}(M)`, so the restriction `H^n(N) → H^n(M)` to the slice
`{1} × M` is injective **exactly when `H^{n-1}(M) = 0`**.  For `M = S⁵ × Y` with `Y` a
product of projective spaces, `H^k(M) = H^k(Y) ⊕ H^{k-5}(Y)` and `Y` has cohomology
only in even degrees, so `H^1(M) = H^3(M) = 0` and the restriction is injective in the
two degrees that matter, `n = 2` and `n = 4`.

(It is *not* injective for all `n ≤ 4`: `H^0(M) ≠ 0` and `H^2(M) ≠ 0` make the `t`
summand nonzero in degrees `1` and `3`.  Chern classes live in even degrees, so only
`n = 2, 4` are ever used.)

Since `δ = W / V` restricts to the trivial total Chern class on the slice, `c₁(δ)` and
`c₂(δ)` restrict to `0` and are therefore `0`.

So the only genuine `K`-theoretic debt in Lemma 3 is `hint` (the integrality
`n! · ch_{n+3}(δ)`), not `hlow`.

## Main results

* `powerSum_eq_zero_of_chernClass_eq_zero` — if the positive Chern classes vanish up
  to degree `N`, so do the power sums.
* `powerSum_eq_zero_of_lt_three` — `hlow` from `c₁(δ) = c₂(δ) = 0`.
-/

namespace GroupApproximation
namespace AlgTop
namespace TotalChern

open Finset (antidiagonal mem_antidiagonal)

variable {A : Type*} [CommRing A]

/-- **Low power sums vanish when the low Chern classes do.**

Newton's identity `q · c_q = ∑_{i+j=q} c_i (-1)^{j+1} p_j` has exactly one term with
`i = 0`, namely `(-1)^{q+1} p_q`; every other term carries a positive Chern class.  So
if `c_1, …, c_N` all vanish, reading the identity at `q ≤ N` leaves `p_q = 0`.  No
splitting hypothesis, no square-zero hypothesis, and no induction. -/
theorem powerSum_eq_zero_of_chernClass_eq_zero (c : TotalChern A) {N : ℕ}
    (h : ∀ k, 0 < k → k ≤ N → c.chernClass k = 0) {q : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    c.powerSum q = 0 := by
  have key := natCast_mul_chernClass c q
  rw [h q hq hqN, mul_zero] at key
  have hmem : ((0 : ℕ), q) ∈ antidiagonal q := by simp
  have hsingle : ∑ ij ∈ antidiagonal q,
      c.chernClass ij.1 * ((-1) ^ (ij.2 + 1) * c.powerSum ij.2)
      = c.chernClass 0 * ((-1) ^ (q + 1) * c.powerSum q) :=
    Finset.sum_eq_single_of_mem ((0 : ℕ), q) hmem (by
      intro b hb hne
      have hb' : b.1 + b.2 = q := mem_antidiagonal.mp hb
      have hb1 : b.1 ≠ 0 := by
        intro h0
        refine hne ?_
        rw [Prod.ext_iff]
        exact ⟨h0, by omega⟩
      rw [h b.1 (Nat.pos_of_ne_zero hb1) (by omega), zero_mul])
  rw [hsingle, chernClass_zero, one_mul] at key
  have hsign : ((-1 : A) ^ (q + 1)) * ((-1 : A) ^ (q + 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc c.powerSum q
      = (((-1 : A) ^ (q + 1)) * ((-1 : A) ^ (q + 1))) * c.powerSum q := by
        rw [hsign, one_mul]
    _ = (-1 : A) ^ (q + 1) * ((-1 : A) ^ (q + 1) * c.powerSum q) := by ring
    _ = 0 := by rw [← key]; ring

/-- **`hlow` of `AlgTop/MappingTorusParity.lean`, from the two low Chern classes.**

This is the hypothesis `∀ q, 0 < q → q < 3 → (W / V).powerSum q = 0`, obtained from
`c₁(δ) = 0` and `c₂(δ) = 0` alone.  In the application `δ = W / V` restricts to the
trivial class on the slice `{1} × M`, and `H^n(S¹ × M) → H^n(M)` is injective for
`n ≤ 4`; see the module docstring. -/
theorem powerSum_eq_zero_of_lt_three (c : TotalChern A)
    (h1 : c.chernClass 1 = 0) (h2 : c.chernClass 2 = 0) :
    ∀ q : ℕ, 0 < q → q < 3 → c.powerSum q = 0 := by
  intro q hq hq3
  refine powerSum_eq_zero_of_chernClass_eq_zero c (N := 2) ?_ hq (by omega)
  intro k hk hk2
  interval_cases k
  · exact h1
  · exact h2

end TotalChern
end AlgTop
end GroupApproximation
