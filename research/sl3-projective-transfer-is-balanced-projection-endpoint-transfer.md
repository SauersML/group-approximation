---
rg: 2
id: sl3-projective-transfer-is-balanced-projection-endpoint-transfer
kind: claim
title: SL3 projective transfer is exactly balanced-projection endpoint transfer
distinct_from:
  commuting-conjugate-involution-is-balanced-overlap: that assumes the two balanced projections commute because of the native lamp relation; the present reduction needs no commutativity and is equivalent to the full arbitrary-unitary projective-transfer wall.
  canonical-iwahori-projection-commutant-transfer: that asks for a canonically decoded positive-density Iwahori projection in a restricted microstate class; the projection here is the half-rank spectral projection of an arbitrary relative-commutant witness.
  projective-trace-square-transfer-for-sl3-pair: that is the still-open estimate; the present claim is an exact reformulation that isolates its sole geometric conclusion.
---

Let

```text
C=SL_3(Z) < A=SL_3(Z[1/2])=<C,h>.
```

The qualitative matrix-ultraproduct form of projective trace-square transfer
is equivalent to the following balanced-projection endpoint statement.
For every asymptotic finite-dimensional representation `rho_n` of `A` and
every projection `P_n` with

```text
tr(P_n)=1/2,
max_(c in S_C) ||P_n-rho_n(c)P_n rho_n(c)^*||_2 -> 0,       (BPE1)
```

put `Q_n=rho_n(h)P_n rho_n(h)^*`.  Then

```text
dist_2(Q_n,{P_n,I-P_n}) -> 0.                              (BPE2)
```

For every balanced projection `P`, every unitary `a`, and `Q=aPa^*`, this
equivalence is governed by the exact, dimension-free identities

```text
tr([(I-2P),a])=4 tr(PQ)-1,

||P-Q||_2^2       =1-2 tr(PQ),
||P+Q-I||_2^2     =2 tr(PQ),                               (BPE3)
```

and hence, with `E=1-|tr([(I-2P),a])|^2`,

```text
2 dist_2(Q,{P,I-P})^2
 <= E
 <=4 dist_2(Q,{P,I-P})^2.                                 (BPE4)
```

Relative to `P H direct_sum (I-P)H`, let `D` and `O` be the total
normalized squared Hilbert--Schmidt mass of the two diagonal and the two
off-diagonal blocks of `a`.  Then

```text
D=2 tr(PQ),       O=1-D,       E=4DO.                     (BPE5)
```

No commutation hypothesis on `P,Q` occurs in `(BPE3)`--`(BPE4)`.
Consequently the full projective SL3 problem is a nonlinear endpoint
selection problem for one half-rank projection, rather than a general
unitary-orbit problem.  The existing rank-one denominator identity removes
the projective ambiguity quantitatively.  In the SL3 packet, vanishing
source and presentation defect give

```text
2 sqrt(O_n) <= 4 sqrt(2 D_n O_n)+o(1).                    (BPE6)
```

Thus every sequence with `liminf O_n>0` has
`liminf D_n>=1/8`.  On every possible enemy, projective target energy and
ordinary off-diagonal block mass are therefore comparable:

```text
(1/2)O_n-o(1) <= E_n <=4O_n.                              (BPE7)
```

Consequently the SL3 claim is equivalently the one-sided conclusion
`||Q_n-P_n||_2->0`; the complementary endpoint cannot occur in an enemy.

This does not establish `(BPE2)`.  It shows precisely why the native
commuting-conjugate lamp is a genuine restriction: that route adds
`[P_n,Q_n]=0`, whereas an arbitrary projective-transfer enemy obtained by
the universal dilation need not have commuting endpoint charts.
