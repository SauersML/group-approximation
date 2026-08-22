---
rg: 2
id: two-chart-trivial-cocycle-order-divides-index-gcd
kind: claim
title: A projective cocycle trivial on two finite charts has order dividing the chart-index gcd
distinct_from:
  projective-holonomy-rank-forces-exponential-multiplicity: that converts a binary commutator form into a representation-multiplicity divisor; this bounds the order of a global cohomology class from two trivial chart restrictions.
  bcs-projective-kernel-phase-compilation: that seeks a phase surviving an infinite tracial payload compiler; this is only a finite two-chart arithmetic screen and supplies no BCS decoder.
---

Let `G` be finite, let `F,Gamma <= G`, and let `[omega] in H^2(G,T)` have
trivial restrictions to both subgroups.  Then

```text
ord([omega]) divides gcd([G:F],[G:Gamma]).             (BTC1)
```

In particular, coprime chart indices force `[omega]=0`.  Thus a finite
two-chart construction cannot hide a global projective phase of order not
supported by the common index arithmetic after both chart restrictions have
been exactified.

For context, Ningyi Li, arXiv:2608.14972, proves for a finite factorization
`G=F Gamma` that

```text
gcd([G:F],[G:Gamma]) exp(G) divides |G|.
```

Combined with `(BTC1)`, this also bounds the exponent of the subgroup of
`H^2(G,T)` consisting of classes trivial on both charts:

```text
exp(H^2_bi-triv(G,T)) exp(G) divides |G|.              (BTC2)
```

The projective-phase screen `(BTC1)` itself is the elementary
restriction--corestriction statement proved in-repository below; only the
factorized-group strengthening `(BTC2)` uses Li's theorem.
