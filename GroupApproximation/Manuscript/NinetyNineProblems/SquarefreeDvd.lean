import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import GroupApproximation.Meta.AxiomGuard

/-!
# Divisibility from the primes, for the strengthened Problem LIX

The strengthened answer to STW Problem LIX produces, at every rank `n ≥ 2`, a
unitary `v` of a separable simple unital C⋆-algebra with

    ∀ k, v ^ k ∈ U₀(A) → ∀ p, p.Prime → p ∣ n → p ∣ k,

so the order of `v` in `U(A)/U₀(A)` is divisible by every prime dividing `n`.
Turning that into "divisible by `n`" is a statement about `ℕ` and about
nothing else, and it is false in general: at `n = 4` the hypothesis gives only
`2 ∣ k`.  It is true exactly when `n` is squarefree, and the three lemmas
below are the arithmetic the C⋆-side endpoint consumes.

They are here rather than beside the endpoint because they mention no
C⋆-algebra, no unitary and no topology.  A reader checking that `6 ∣ k`
follows should not have to load the construction to do it.

* `squarefree_dvd_of_forall_prime_dvd` — the squarefree corollary.
* `six_dvd_of_forall_prime_dvd` — the headline instance, proved from
  coprimality rather than as a special case, so that it does not depend on
  `Squarefree 6` being available by decision.
* `not_forall_prime_dvd_one` — why `v ∉ U₀(A)` needs no separate clause: the
  power clause at `k = 1` already gives it, because `2 ≤ n` supplies a prime
  divisor of `n` and no prime divides `1`.
-/

namespace GroupApproximation
namespace NinetyNineProblems

/-- **The squarefree corollary, as arithmetic.**  If every prime dividing `N`
divides `k` and `N` is squarefree, then `N` divides `k`.

Squarefreeness is what makes the primes enough: `N` is the product of its
distinct prime factors, and a product of distinct primes divides `k` as soon
as each factor does.  Without it the statement fails at `N = 4`, `k = 2`. -/
theorem squarefree_dvd_of_forall_prime_dvd {N k : ℕ} (hsq : Squarefree N)
    (h : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ k) : N ∣ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact dvd_zero N
  have hprod : ∏ p ∈ N.primeFactors, p = N := Nat.prod_primeFactors_of_squarefree hsq
  have hsub : N.primeFactors ⊆ k.primeFactors := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, h p hp.1 hp.2.1, hk⟩
  have hdvd : ∏ p ∈ N.primeFactors, p ∣ k := (Nat.prod_primeFactors_dvd_iff hk).mpr hsub
  rwa [hprod] at hdvd

/-- **The headline instance.**  If every prime dividing `6` divides `k` then
`6` divides `k`.

`6` is the smallest number that is neither a prime power nor `1`, which is why
it is the instance worth printing: the two primes are supplied by two
independent mod-`p` arguments at one algebra.  Proved from `Nat.Coprime`
rather than from `squarefree_dvd_of_forall_prime_dvd`, so that it rests on no
decision procedure. -/
theorem six_dvd_of_forall_prime_dvd {k : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ 6 → p ∣ k) : 6 ∣ k := by
  have h2 : (2 : ℕ) ∣ k := h 2 Nat.prime_two (by norm_num)
  have h3 : (3 : ℕ) ∣ k := h 3 Nat.prime_three (by norm_num)
  have hcop : Nat.Coprime 2 3 :=
    (Nat.coprime_primes Nat.prime_two Nat.prime_three).mpr (by norm_num)
  have hmul : (2 : ℕ) * 3 ∣ k := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 h3
  have hsix : (2 : ℕ) * 3 = 6 := by norm_num
  rwa [hsix] at hmul

/-- **No prime divides `1`**, in the form the endpoint uses: for `2 ≤ n` the
condition "every prime dividing `n` divides `k`" fails at `k = 1`.

This is the whole of why the strengthened statements carry no `v ∉ U₀(A)`
conjunct.  Reading the power clause at `k = 1` turns `v ∈ U₀(A)` into
`∀ p, p.Prime → p ∣ n → p ∣ 1`, which this refutes. -/
theorem not_forall_prime_dvd_one {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ 1 := by
  intro h
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
  have hle : p ≤ 1 := Nat.le_of_dvd Nat.one_pos (h p hp hpn)
  have := hp.two_le
  omega

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms squarefree_dvd_of_forall_prime_dvd
#audit_axioms six_dvd_of_forall_prime_dvd
#audit_axioms not_forall_prime_dvd_one
