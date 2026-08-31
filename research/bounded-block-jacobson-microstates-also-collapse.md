---
rg: 2
id: bounded-block-jacobson-microstates-also-collapse
kind: claim
title: Jacobson head-retaining microstates must put positive trace mass in unbounded irreducible blocks
distinct_from:
  bounded-dimension-jacobson-head-has-algebraic-collapse: that treats one tuple of bounded total dimension; this is stable under arbitrarily many direct sums and quantifies the trace mass which must escape every fixed block size
  jacobson-property-t-and-finite-k-do-not-exactify-the-head: that isolates the global normalized-HS modulus; this rules out the entire subhomogeneous part of any putative countersequence
  qutrit-complementary-jacobson-signs-minimal-router-finite: that gives a finite packet model; this shows bounded finite-packet sectors cannot carry the head in a full-presentation microstate
---

Fix the finite presentation and head word from
`bounded-dimension-jacobson-head-has-algebraic-collapse`. For a unitary
`Sigma`-tuple `U`, decompose the finite-dimensional C-star algebra it
generates into irreducible matrix blocks. Let `mu_D(U)` be the normalized
dimension carried by blocks of size greater than `D`, including
multiplicity.

For every `D>=1` there are constants `K_D<infinity` and
`beta_D>0` such that

```text
||w(U)-I||_2^2
 <= K_D^2 |R|^beta_D delta(U)^(2 beta_D)+4 mu_D(U),      (BBJ1)

delta(U)=max_(r in R)||r(U)-I||_2.
```

The constants are independent of the total matrix dimension, the number of
blocks, and their multiplicities.

Consequently, if `delta(U_k)->0` while

```text
||w(U_k)-I||_2>=epsilon>0,
```

then for every fixed `D`,

```text
liminf_(k->infinity) mu_D(U_k) >= epsilon^2/4.           (BBJ2)
```

In particular a head-retaining sequence cannot be subhomogeneous with any
fixed degree. More strongly, a nonvanishing fraction of its normalized
trace must escape beyond every bounded irreducible size. Merely repeating
bounded-dimensional complementary-sign packets can never produce a
full-presentation countersequence.

This does not rule out genuinely large irreducible microstates. It sharpens
the surviving gate from total dimension growth to positive-trace
irreducible-size escape.

DERIVATION
direct-sum-concavity-preserves-head-modulus-proof
