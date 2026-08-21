---
rg: 2
id: fk-transfer-needs-uniform-log-integrability
kind: claim
title: Fuglede--Kadison determinant transfer requires uniform logarithmic-tail integrability
distinct_from:
  index-density-is-amplification-stable: that normalizes an integer-valued index against dimension; this concerns the unbounded logarithm at zero and the extra spectral-tail hypothesis needed for determinant convergence.
  iwahori-cycle-packet-determinant-fence: that uses a finite packet determinant identity inside a controlled representation sector; this states the general analytic limit theorem for polynomial evaluations on arbitrary regular microstates.
---

Let `U_n` converge in star moments to `u`, let `P` be a fixed square matrix
of noncommutative polynomials, and put

```text
A_n=P(U_n)^*P(U_n),        A=P(u)^*P(u).
```

The spectral probability measures `mu_n` of `A_n` converge weakly to the
spectral measure `mu` of `A`. Consequently, for every fixed `epsilon>0`,

```text
(1/2) tr(log(A_n+epsilon I)) -> (1/2) tau(log(A+epsilon I)).
```

Unregularized normalized log determinants do **not** follow from moment
convergence, even when `A` has a spectral gap and every `A_n` is invertible.
They transfer if the negative logarithmic tails are uniformly integrable:

```text
lim_(delta down to 0) sup_n integral_(0,delta) |log t| d mu_n(t) = 0.
```

A common finite-model lower bound `A_n>=cI`, `c>0`, is sufficient. A lower
bound on `A` alone controls only the proportion of exceptional singular
values and not their size.
