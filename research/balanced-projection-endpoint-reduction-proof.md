---
rg: 2
id: balanced-projection-endpoint-reduction-proof
kind: route
title: Convert projective commutator energy into balanced projection endpoint distance
target: sl3-projective-transfer-is-balanced-projection-endpoint-transfer
requires:
  - trace-zero-involution-projective-transfer-equals-rcc
  - projective-transfer-equals-rcc-for-perfect-pairs
  - sl3-rank-one-denominator-self-commutator-removes-target-phase
---

Let `v=I-2P`, where `P` is a projection of normalized trace `1/2`, and put
`Q=aPa^*`.  Direct multiplication, with no use of `[P,Q]=0`, gives

```text
[v,a]=vava^*=(I-2P)(I-2Q),
tr([v,a])=1-2tr(P)-2tr(Q)+4tr(PQ)=4tr(PQ)-1.              (R1)
```

The scalar `tr(PQ)` is real and belongs to `[0,1/2]`, since
`tr(PQ)=tr(PQP)`.  Traciality also gives

```text
||P-Q||_2^2
 =tr(P)+tr(Q)-tr(PQ)-tr(QP)=1-2tr(PQ),

||P+Q-I||_2^2
 =1-tr(P)-tr(Q)+tr(PQ)+tr(QP)=2tr(PQ).                   (R2)
```

Write `x=2tr(PQ)` and `m=min{x,1-x}`.  Then

```text
E:=1-|tr([v,a])|^2=1-(2x-1)^2=4x(1-x),
dist_2(Q,{P,I-P})^2=m.                                  (R3)
```

For `0<=x<=1`, one has `m/2<=x(1-x)<=m`, which proves
`2m<=E<=4m`.

We now compare failure sequences.  A sequence of balanced projections
satisfying `(BPE1)` but violating `(BPE2)` gives trace-zero involutions
`v_n=I-2P_n` which centralize `rho_n(C)` asymptotically and retain positive
projective `h`-energy by `(R3)`.  Thus it directly violates qualitative
projective transfer.

Conversely, suppose qualitative projective transfer fails.  By
`projective-transfer-equals-rcc-for-perfect-pairs`, it gives an ordinary
relative-commutant leak in a tracial matrix ultraproduct.  Apply
`trace-zero-involution-projective-transfer-equals-rcc`: after a fixed
two-by-two amplification the leak is witnessed by trace-zero self-adjoint
involutions `v_n`, with a uniform positive target energy.  Functional
calculus changes `v_n` by `o(1)` so that

```text
P_n=(I-v_n)/2
```

are exact trace-half projections.  Ordinary asymptotic centrality of `v_n`
is exactly `(BPE1)`, and `(R3)` makes their endpoint distance uniformly
positive.  This violates `(BPE2)`.

Finally, when endpoint transfer holds, `(R3)` gives vanishing projective
target energy.  The explicit SL3 rank-one denominator estimate in
`sl3-rank-one-denominator-self-commutator-removes-target-phase` upgrades the
commutator from closeness to a scalar to closeness to `I`.  In projection
language this excludes `Q_n=I-P_n+o(1)` and selects `Q_n=P_n+o(1)`.

The already established tensor-amplification linearization then converts
this qualitative equivalence into the same dimension-free linear-modulus
question as the original projective trace-square inequality.  No exactness
or correction of the ambient approximate representation has been assumed.
