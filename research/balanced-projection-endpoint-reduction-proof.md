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

There is also a useful block form.  Relative to `P H direct_sum (I-P)H`,
unitarity and equality of the two block ranks give

```text
||PaP||_2^2=||(I-P)a(I-P)||_2^2=tr(PQ),
||Pa(I-P)||_2^2=||(I-P)aP||_2^2=1/2-tr(PQ).              (R4)
```

Hence the total diagonal and off-diagonal masses are `D=x`, `O=1-x`, and
`E=4DO`.

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

Finally the explicit SL3 rank-one denominator estimate gives more than
asymptotic endpoint selection.  Since

```text
||[v,a]-I||_2^2=2-2tr([v,a])=4O,                         (R5)
```

its estimate, on a sequence with vanishing source and presentation defect,
reads

```text
2 sqrt(O)<=2 sqrt(2E)+o(1)=4 sqrt(2DO)+o(1).             (R6)
```

If `O` does not vanish, division along a positive-mass subsequence gives
`liminf D>=1/8`.  Therefore `E=4DO` is bounded below by
`O/2-o(1)` on every possible enemy, while always `E<=4O`.  Projective
transfer is consequently equivalent, for this SL3 presentation, to the
one-sided balanced projection conclusion `||P-aPa^*||_2->0`; the
complementary branch is quantitatively unavailable.

The already established tensor-amplification linearization then converts
this qualitative equivalence into the same dimension-free linear-modulus
question as the original projective trace-square inequality.  No exactness
or correction of the ambient approximate representation has been assumed.
