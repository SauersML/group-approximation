---
rg: 2
id: proper-torus-reynolds-divergence-proof
kind: route
title: Primitive-divisor relative girth and super-approximation force Reynolds Green divergence
target: proper-torus-reynolds-is-edge-refinement
requires: []
---

The target contains the complete proof.  Briefly, the two cubic normal
subgroups generate `C_3*C_3` in `PSL_2(Z[1/2])` and meet the signed split
torus normalizer trivially.  Entry-height control therefore gives relative
girth `log_6 M`.  Choosing a square-free modulus from primitive divisors of
`4^k-1` makes this girth `Omega(n log n)` while the signed normalizer orbit
has size only `exp(O(n))`.

Salehi Golsefidy's square-free super-approximation theorem gives a uniform
spectral gap for the finite images of this fixed Zariski-dense group.  The
associated bipartite incidence components inherit the gap by the explicit
two-endpoint walk comparison.  The electrical transfer kernel consequently
decays exponentially off the diagonal.  Thus the cut projection of the
signed normalizer-orbit source retains a fixed bypass current at every
orbit edge.  Divergence-free flux through the disjoint tree shells around
those edges forces `l_1` mass `Omega(|N| log M)`.

After the normalized signed Reynolds average this is an
`Omega(log M)` infinity-norm lower bound for the cut projection.  The
Moore--Penrose identity `C_H^dagger C_H=P_chi P_cut` transfers it to
`C_H^dagger`.  Removing the norm-one fiber-constant projection subtracts
only the uniformly bounded full-torus block, so the divergence occurs in
the required fiber-mean-zero proper-torus sector.
