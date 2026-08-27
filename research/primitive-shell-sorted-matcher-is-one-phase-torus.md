---
rg: 2
id: primitive-shell-sorted-matcher-is-one-phase-torus
kind: claim
title: The sorted primitive-shell matcher has one phase torus and a parity-corrected doubling law
artifacts:
  - research/primitive-shell-sorted-matcher-is-one-phase-torus-proof.md
distinct_from:
  primitive-shell-bs-clock-has-optimal-opnorm-matcher: that proves existence and optimal scale of a matcher; this identifies the sorted matched conjugate, its exact parity cocycle, and all unitaries realizing that same conjugate.
  three-higman-bs-seams-vanish-fourth-is-product-holonomy: that leaves four independent packet gauges in a general HS cycle; this reduces the homogeneous primitive-shell sorted gate to one explicit L-dimensional phase torus.
---

**ESTABLISHED.**  Put `q=3^n`, `L=2q/3`, and index the primitive unit-shell
basis by exponents:

```text
e_a := e_(2^a mod q),             a in Z/LZ.
```

Then `P e_a=e_(a-1)`.  Let `omega=exp(2 pi i/L)` and define the rank
permutation

```text
f(a)=floor(2 u_a/3),
u_a in {1,...,q-1},   u_a=2^a mod q.                 (SPT1)
```

The diagonal unitary

```text
B e_a=omega^(f(a)) e_a                              (SPT2)
```

is the sorted spectral conjugate of `P` used by
`primitive-shell-bs-clock-has-optimal-opnorm-matcher`.  It satisfies

```text
f(a+1)=2f(a)+1_(f(a) even)       mod L,              (SPT3)
||P B P^*-B^2||_op=|omega-1|=2sin(pi/L).             (SPT4)
```

Choose one unitary `H` with `H P H^*=B`.  Since both spectra are simple,
every unitary producing this same sorted conjugate is exactly

```text
K=R H,       R diagonal unitary.                     (SPT5)
```

Equivalently the apparent right `P`-centralizer phase is absorbed into the
left diagonal phase after applying `H`; there are `L`, not `2L`, independent
phases (up to the irrelevant common scalar).  In the exponent basis, `H` is
a row-permuted Fourier matrix and hence

```text
|H_(a,b)|=L^(-1/2).                                  (SPT6)
```

Consequently the exact sorted fourth-return problem is the explicit compact
optimization

```text
inf_(R diagonal unitary)
 ||(R H)^4 P (R H)^(-4)-P||_op.                      (SPT7)
```

This claim neither evaluates `(SPT7)` nor covers matchers which mix several
nearby spectral values instead of diagonalizing `P` exactly.  It removes a
spurious second gauge torus and records the arithmetic cocycle that any
analytic lower bound for the sorted matcher must consume.
