---
rg: 2
id: fixed-clifford-sectors-have-zero-adjacent-opposite-overlap
kind: claim
title: Successive fixed Clifford sectors have zero opposite Iwahori overlap
distinct_from:
  fixed-clifford-projective-dyadic-tower: that identifies the full projective inertia category over the invariant newest-layer character and its conductor shift; this computes the adjacent opposite pullback and proves that the shifted restriction exits that invariant sector.
  sparse-dyadic-iwahori-packets-have-a-uniform-boundary: that gives a two-thirds flow constraint for arbitrary exact-conductor packets; this gives literal zero overlap for the proposed recursive fixed-character packet, with no loss constant.
  iwahori-dual-inclusion-graph-is-fusion-not-the-bruhat-tits-tree: that shows a one-sided Clifford orbit is fusion-closed; this shows the opposite depth shift sends the fixed orbit into a different, size-three orbit.
---

For `a>=3`, let `C_a` be the full subcategory of representations of

```text
G_a=SL_2(Z/2^a)
```

on whose newest congruence layer `L_a` the invariant Clifford character

```text
ell_0(A,B,C)=A+B+C
```

acts.  If `pi in C_a` and `rho in C_(a+1)`, then their upper/opposite
Iwahori restrictions have no common constituent:

```text
Hom_B(pi o q_a, rho o q_(a+1) o sigma)=0.               (FZO1)
```

This remains true for arbitrary direct sums and multiplicities in the two
fixed-character sectors.  Hence the projective categories
`Rep_(omega_a)(G_(a-1))` supplied by invariant-character Clifford theory
cannot recursively realize even one edge of the saturated diffuse flow by
matching the fixed sector at depth `a` to the fixed sector at depth `a+1`.

More precisely, any level-`a+1` irreducible whose opposite restriction has
nonzero overlap with a level-`a` fixed-sector upper restriction must lie over
the size-three newest-layer orbit

```text
O_B={(0,1,0),(0,1,1),(0,0,1)},                          (FZO2)
```

not over the invariant orbit `{(1,1,1)}`.  Its inertia group is the
index-three preimage of the stabilizer of `(0,1,0)` in
`SL_2(F_2)=S_3`, rather than all of `G_(a+1)`.  Thus the adjacent extension
loses the full-inertia projective tower immediately.  Any genuine diffuse
packet must alternate between different Clifford orbits and their inertia
categories; iterating only the canonical multipliers `omega_a` is
algebraically impossible.

