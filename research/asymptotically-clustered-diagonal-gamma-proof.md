---
rg: 2
id: asymptotically-clustered-diagonal-gamma-proof
kind: route
title: Fourier-mix uniformly close eigenmaps and discard only the packet remainder
target: asymptotically-clustered-diagonal-ah-has-uniform-gamma
requires: []
artifacts:
  - research/artifacts/stw99-xx-clustered-eigenmap-gamma-2026-08-30.md
---

Fix `k>=2`, a stage `n`, and a finite set `F` in the unit ball.  Choose a
later composite and a packet decomposition as in the claim, with error
`epsilon`.  On a good packet `I_t`, reorder its blocks and identify their
sum with `M_k tensor M_(r_n)`.  Let

```text
q_1,...,q_k in M_k
```

be the rank-one projections onto the Fourier basis.  Thus they are mutually
orthogonal, sum to `1`, and every diagonal entry of every `q_ell` is `1/k`.
Put `q_ell tensor 1_(r_n)` on this packet.  On each exceptional block in
`R`, assign the entire block to one arbitrary colour.  Taking direct sums,
then conjugating by the continuous unitary which gives the diagonal form,
produces continuous projections

```text
p_1,...,p_k in C(X_m) tensor M_(r_m)
```

which are orthogonal and sum to one.

For `a in F` and a good packet, put

```text
D(y)=diag(a(lambda_i(y)))_(i in I_t).
```

Choose one index `i_0` in the packet and let `D_0(y)` repeat
`a(lambda_(i_0)(y))` in every block.  The packet projection commutes with
`D_0(y)`, while `||D(y)-D_0(y)||<epsilon`.  Hence

```text
||[q_ell tensor 1,D(y)]|| < 2 epsilon.                 (CEG1)
```

The exceptional block projections commute exactly with `D(y)`.  Therefore
`||[p_ell,phi_(n,m)(a)]||<2 epsilon` for every `a in F`.

The trace estimate is stronger and does not use closeness.  Flatness of the
Fourier projection's diagonal gives, on every good packet and at every base
point,

```text
tr((q_ell tensor 1)D) = (1/k) tr(D),
```

where both traces are normalized relative to the full later fibre.  Only
the exceptional blocks contribute an error.  Since `F` is in the unit ball,

```text
sup_(y in X_m)
 |tr_(r_m)(p_ell phi_(n,m)(a))(y)
       -(1/k)tr_(r_m)(phi_(n,m)(a))(y)|
 <= |R|/L < epsilon.                                  (CEG2)
```

Every tracial state on the later homogeneous block integrates normalized
fibre traces, so `(CEG2)` is uniform over the restrictions of all limit
traces.

For this fixed `k`, diagonalize over increasing stages, finite sets with
dense union, and `epsilon` tending to zero.  Equation `(CEG1)` makes the
resulting partitions norm central, while `(CEG2)` gives uniform mixed-trace
splitting on a dense subset and hence on all of `A`.  Their classes in the
uniform tracial ultrapower are the projections required for uniform
property Gamma.  Since this construction works separately for every
`k>=2`, the proof is complete.

For the stated equal-eigenmap corollary, partition the multiplicity of each
distinct eigenmap into `k`-tuples.  At most `k-1` copies of each of the
`D_(n,m)` eigenmaps remain, so

```text
|R|/L <= (k-1)D_(n,m)/L -> 0,
```

and the within-packet error is exactly zero.
