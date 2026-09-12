---
rg: 2
id: atlas-m2-kernel-phases-have-rank-path-barrier
kind: claim
title: The two multiplicity-two kernel phases connect by bounded-rank steps but pay a linear residual barrier
distinct_from:
  atlas-m2-kernel-phases-cannot-upper-toeplitz-stitch: that treats arbitrary off-diagonal upper-triangular couplings through invariant flag quotients; this computes the rank-metric separation and the canonical bounded-step path inside the exact packet-zero locus.
  atlas-multiplicity-two-joint-kernel-slice-is-empty: that gives the finite rank-pair spectrum; this turns its two pure fibers into all-amplification metric estimates.
  sublinear-bandwidth-is-vacuous-under-rank-amplification: that removes a basis-dependent bandwidth restriction from arbitrary rank microstates; this retains the packet-zero condition at every step and measures both kernel residuals exactly.
---

Choose multiplicity-two packet-zero gauges `A,B in GL8(F2)` from one marking
parity with

```text
rank(q_19243(A)-I)=0,     rank(q_14(A)-I)=1,
rank(q_19243(B)-I)=2,     rank(q_14(B)-I)=0.          (RPB1)
```

Let `A_N=A^(direct_sum N)` and `B_N=B^(direct_sum N)`, acting in dimension
`8N`.  If `H_N` denotes the full packet-zero q14-zero stratum in that
dimension and `C_N` the full packet-zero collision-zero stratum, then

```text
dist_rank(A_N,H_N)/(8N) >=1/32,
dist_rank(B_N,C_N)/(8N) >=1/32.                       (RPB2)
```

Thus the two pure amplified phases do not approach the opposite exact zero
stratum in normalized rank.

Nevertheless the packet-zero gauge space has a bounded-rank path between
them.  Put

```text
T_j=A^(direct_sum (N-j)) direct_sum B^(direct_sum j),
0<=j<=N.                                               (RPB3)
```

Every packet residual is zero, and

```text
rank(T_(j+1)-T_j)<=8,
rank(q_14(T_j)-I)=N-j,
rank(q_19243(T_j)-I)=2j.                              (RPB4)
```

Consequently

```text
max(rank(q_14(T_j)-I),rank(q_19243(T_j)-I))
 >=ceil(2N/3)                                         (RPB5)
```

at every point of this canonical path, and the residual-rank sum is at least
`N`.  Bounded-rank adjacency therefore exists, but the obvious phase path is
not a noncommutative Folner escape: its incompatibility remains at positive
density rather than localizing at one transition.

For the full multiplicity-`m` strata, define

```text
alpha_m=min_(T in C_m) rank(q_14(T)-I),
beta_m =min_(T in H_m) rank(q_19243(T)-I).             (RPB6)
```

Laurent-word Lipschitzness gives the general invariant

```text
dist_rank(C_m,H_m)>=max(alpha_m/4,beta_m/8).           (RPB7)
```

The m2 calibration gives the analogous pair `(1,2)` only on its F4-seeded
slice.  Whether `alpha_m/m` or `beta_m/m` stays uniformly positive on the
**full** packet-zero strata is exactly the surviving rank-separation question;
no existing finite-slice or amplification argument proves it.
