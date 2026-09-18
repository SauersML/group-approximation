import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import GroupApproximation.Meta.AxiomGuard

/-!
# Killing primes, part 5: substituting `X ↦ X^N + C b` makes a polynomial monic

Lane `bh-met-91t`.  `f : A →+* B[X]`, `g : A[X]` of degree `e`, with `f (lc g)` monic and
`deg f (g_i) < N` for `i < e`.  Then `g.eval₂ f (X^N + C b)` is monic: the top term
`f (lc g) (X^N + C b)^e` is monic of degree `deg f(lc g) + e N`, and the others have degree
`≤ (N - 1) + i N ≤ e N - 1`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

theorem suslinKill_monic_eval₂ {A B : Type*} [CommRing A] [CommRing B] [Nontrivial B]
    (f : A →+* B[X]) (b : B) (N : ℕ) (hN : 0 < N) (g : A[X])
    (hlc : (f g.leadingCoeff).Monic)
    (hlow : ∀ i < g.natDegree, (f (g.coeff i)).natDegree < N) :
    (g.eval₂ f (X ^ N + Polynomial.C b)).Monic := by
  have hT : (X ^ N + Polynomial.C b : B[X]).Monic := monic_X_pow_add_C b (by omega)
  have hTd : (X ^ N + Polynomial.C b : B[X]).natDegree = N := natDegree_X_pow_add_C
  have hco : g.coeff g.natDegree = g.leadingCoeff := rfl
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, hco]
  have htop : (f g.leadingCoeff * (X ^ N + Polynomial.C b) ^ g.natDegree).Monic :=
    hlc.mul (hT.pow g.natDegree)
  rcases Nat.eq_zero_or_pos g.natDegree with h0 | hpos
  · rw [h0, Finset.sum_range_zero, zero_add, pow_zero, mul_one]
    exact hlc
  refine htop.add_of_right (degree_lt_degree ?_)
  have htopd : (f g.leadingCoeff * (X ^ N + Polynomial.C b) ^ g.natDegree).natDegree =
      (f g.leadingCoeff).natDegree + g.natDegree * N := by
    rw [hlc.natDegree_mul (hT.pow g.natDegree), hT.natDegree_pow, hTd]
  rw [htopd]
  have hEN : 1 * 1 ≤ g.natDegree * N := 
    Nat.mul_le_mul (by omega : 1 ≤ g.natDegree) (by omega : 1 ≤ N)
  have hle : (∑ i ∈ Finset.range g.natDegree,
      f (g.coeff i) * (X ^ N + Polynomial.C b) ^ i).natDegree ≤ g.natDegree * N - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    have h1 := hlow i hi
    have h2 : ((X ^ N + Polynomial.C b : B[X]) ^ i).natDegree ≤ i * N := by
      have h := natDegree_pow_le (p := (X ^ N + Polynomial.C b : B[X])) (n := i)
      rwa [hTd] at h
    have h3 : i * N + N ≤ g.natDegree * N := by
      rw [← add_one_mul]
      exact Nat.mul_le_mul_right N (by omega)
    calc (f (g.coeff i) * (X ^ N + Polynomial.C b) ^ i).natDegree
        ≤ (f (g.coeff i)).natDegree + ((X ^ N + Polynomial.C b : B[X]) ^ i).natDegree :=
          natDegree_mul_le
      _ ≤ g.natDegree * N - 1 := by omega
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_monic_eval₂

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
