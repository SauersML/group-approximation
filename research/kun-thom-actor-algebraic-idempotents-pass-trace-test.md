---
rg: 2
id: kun-thom-actor-algebraic-idempotents-pass-trace-test
kind: claim
title: Every idempotent in a matrix algebra over C[G] for a Kun--Thom Theorem E actor has trace in the finite-subgroup ring
distinct_from:
  zalesskii-idempotent-trace-is-rational: that shows idempotent traces are rational for every group; this confines their denominators to the primes of P(q,r,d) on the Theorem E actors, through congruence quotients chosen by Dirichlet.
  subgroup-average-projections-give-no-reduced-bc-obstruction: that disposes of subgroup averages and Kazhdan projections; this disposes of every algebraic idempotent, in particular every spectral projection of a finite-spectrum element.
  kadison-kaplansky-torsion-free: that is the torsion-free projection conjecture for reduced algebras; this is an unconditional trace theorem for algebraic idempotents on one class of groups with torsion, and says nothing about non-algebraic projections.
  small-capacity-kk-witnesses-are-algebraic-idempotents: that turns small-capacity gapped witnesses into algebraic idempotents for any group; this shows such idempotents cannot refute the trace test on the Theorem E actors.
artifacts:
  - research/artifacts/bc-kun-thom-trace-test-2026-09-12.md
---

**ESTABLISHED.** Let `G = EL_r(F_q[x_1^(+-1), ..., x_d^(+-1)]) semidirect SL_d(Z)` with `r, d >= 3`,
a Kun--Thom Theorem E actor. For every `n` and every idempotent `e ∈ M_n(C[G])`,

```text
tau(e) = sum_i e_ii(1)  lies in  Z[1/P(q,r,d)] = Lambda^G.
```

**Corollary.** Let `a = a* ∈ M_n(C[G])`, and suppose `lambda(a)` has finite spectrum in
`M_n(C*_r G)`. Then every spectral projection of `lambda(a)` is a polynomial in `a`, so it is an
idempotent of `M_n(C[G])` and its trace lies in `Lambda^G`. No finite-spectrum element refutes
Lück's trace test on a Theorem E actor.

**Consequence for `baum-connes-counterexample-group-exists`.** A projection refuting the trace test
on these groups must be non-algebraic: it lies in `M_n(C*_r G)` but not in the image of
`M_n(C[G])`. For `a ∈ M_n(Z[i][G])`, `integral-spectra-of-small-capacity-are-finite` then forces the
spectrum to have logarithmic capacity at least 1. The trace of a gapped spectral projection is the
limit of rational eigenvalue fractions over the congruence quotients `G/N_(p')`, and nothing in the
graph controls that limit (artifact, Section 4).

The mechanism works over any coefficient field `C`, uses no approximation property, and gives
rationality without Zalesskii. The general principle is elementary: an idempotent pushed to a
finite quotient avoiding its support has trace in `(1/|F|) Z`. It is very likely known; novelty
is claimed only for the Dirichlet choice of congruence quotients for these groups.
