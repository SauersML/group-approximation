---
rg: 2
id: orthogonal-odd-cut-join-amplifies-boundary-linearly
kind: claim
title: Even orthogonal odd cuts can amplify join boundary by a linear factor
distinct_from:
  join-of-odd-cuts-softens-an-entire-anchor-row: that proves one-shot operator-small coverage and isolates the join boundary; this gives a finite-dimensional obstruction to charging that boundary by anchor-tail energy alone.
  monotone-anchor-sign-budget-does-not-give-stagewise-coverage: that uses many central zero-boundary spikes to obstruct sequential coverage; this uses one joined cut whose boundary is macroscopic despite vanishing averaged input energies.
  anchor-reset-row-sign-trace-is-sharp-lyapunov: that absorbs created boundary energy into an order-one sign reservoir; this shows why the join boundary cannot instead be bounded by the small anchor tail without extra parity structure.
---

ESTABLISHED SHARP OBSTRUCTION.  There is a family of an anchor reflection
`A`, site reflections `B_1,...,B_L`, and pairwise orthogonal projections
`p_i=1_[s,1](Y_i^2)` for every fixed `0<s<=1`, where

```text
 Y_i=(B_i-AB_iA)/2,
 p=join_i p_i,
```

such that

```text
 (1/L)sum_i tau(Y_i^2 1_[s,1](Y_i^2)) =1/(2L),         (OJA1)
 (1/L)sum_i ||[A,B_i]||_2^2             =2/L,          (OJA2)
 (1/L)sum_i ||[p,B_i]||_2^2             =1-1/L.        (OJA3)
```

Moreover

```text
 (1/L^2)sum_(i,j)||[B_i,B_j]||_2^2=4(L-1)/L^2.         (OJA4)
```

Thus the join boundary is macroscopic while both the anchor row and the
complete-pair site energy vanish.  In particular, no dimension-independent
constant `C` can make any of

```text
 D(p)<=C s^(-1) avg_i tau(Y_i^2 1_[s,1](Y_i^2)),
 D(p)<=C s^(-1) avg_i ||[A,B_i]||_2^2,
 D(p)<=C s^(-1)(anchor-row energy + site-pair energy)   (OJA5)
```

hold for arbitrary reflection tuples.  The failure is not caused by
noncommutativity among the cuts: the `p_i` here are orthogonal.

Consequently the join in
`join-of-odd-cuts-softens-an-entire-anchor-row` cannot be charged using only
spectral coarea, anchor-row tails, or the complete commutation overlay.  A
successful estimate must use the all-dual parity/Loewner relations to forbid
the construction's behavior, retain site labels rather than take the bare
join, or accept the order-one sign reservoir from
`anchor-reset-row-sign-trace-is-sharp-lyapunov`.  This claim does not show
that the balanced parity presentation admits the obstruction; its parity
face energy has not been made small.
