---
rg: 2
id: promislow-unit-conjecture-from-shadow-monomial-fp-units
kind: claim
title: Higman's unit conjecture for the Promislow group follows once shadow-monomial units of F_p[P] are trivial for infinitely many primes p
distinct_from:
  promislow-integral-units-have-monomial-definite-line-shadows: that proves integral units have monomial definite shadows; this turns that fact into a sufficient characteristic-p criterion for triviality of all integral units.
  promislow-classical-nontrivial-units-have-no-integral-lifts: that excludes finitely many named residues as reductions of integral units; this reduces the whole integral conjecture for P to units of F_p[P] with monomial shadows.
  integral-unit-conjecture-torsion-free: that is Higman's conjecture for every torsion-free group; this is a criterion for the single group P that proves nothing unconditionally.
---

**ESTABLISHED** (a criterion; it proves no triviality). Let `P` be the Promislow
group and, for a prime `p`, let `SM_p` be the set of units `w` of `F_p[P]` whose
three definite shadows `A, B, C` in `D(F_p)`
(`promislow-integral-units-have-monomial-definite-line-shadows`) are all of the
form `+-t^m` or `+-t^m u`.

1. **Sufficient criterion.** If there are infinitely many primes `p` such that
   every element of `SM_p` is `lambda g` with `lambda in F_p^x` and `g in P`,
   then every unit of `Z[P]` is `+-g` and every unit of `Q[P]` is `lambda g`.
2. **What a counterexample produces.** If `v in Z[P]^x` is not `+-g`, then for
   every prime `p > 2 max_g |v(g)|` the reduction of `v` modulo `p` lies in
   `SM_p`, is not `lambda g`, and has the same support as `v`.

So Higman's conjecture for `P` holds as soon as shadow-monomial units in
characteristic `p` are trivial along an infinite set of primes. Conversely, a
counterexample yields nontrivial shadow-monomial units of one fixed support in
every large characteristic.

**Scope.** The hypothesis of item 1 fails at `p = 2, 3, 5, 7`
(`promislow-fp-has-nontrivial-shadow-monomial-units`): twists of Gardam's unit
and commutators of Murray's units with `z` are nontrivial units with monomial
shadows. It is not known for any prime. So this criterion, as stated, gives no
route unless shadow-monomial units become trivial at larger primes, and the
commutator mechanism suggests they do not. Item 2 is the useful direction: it
describes what a counterexample must look like in every large characteristic.
No novelty is claimed.

DERIVATION
[[promislow-unit-conjecture-shadow-monomial-fp-reduction-proof]]
