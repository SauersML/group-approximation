---
rg: 2
id: oriented-schur-restriction-mass-identity
kind: claim
title: An active Schur rank jump gives an exact half-return identity with only inactive leakage
distinct_from:
  predicate-rank-gate-doubles-restriction-multiplicity: that computes the restriction of each simple packet sector; this sums those restrictions against an oriented marked multiplicity functional and isolates the sole leakage term.
  coherent-sequential-schur-tape-payment: that performs perturbative alignment along every tape incidence; this is its exact one-cell scalar calculation.
---

Let a finite packet inclusion `A<=B` have simple sectors indexed by `x`, and
suppose the `B`-simple `T_x` restricts to the corresponding `A`-simple as

```text
T_x downarrow_A = S_x^(direct sum 2^f(x)),       f(x) in {0,1}.
```

Let `m(x)>=0` be arbitrary `B`-multiplicities and let `h(x) in [0,1]` be any
marked-sector weight. Define

```text
a_B   =sum_x h(x)m(x),
a_A   =sum_x h(x)2^f(x)m(x),
b_inactive=sum_(x:f(x)=0) h(x)m(x).
```

Then

```text
a_B=(1/2)a_A+(1/2)b_inactive.                                 (OSR1)
```

Thus if `f=1` is chosen on the propagation-satisfying sectors, the desired
factor `1/2` is exact and every failure of doubling is supported on a
constraint-violating selector sector. No estimate, integrality limit, or
choice of irreducible copies is involved.

