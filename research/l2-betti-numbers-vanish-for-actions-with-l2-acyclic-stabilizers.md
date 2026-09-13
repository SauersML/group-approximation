---
rg: 2
id: l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers
kind: claim
title: A group acting on an m-acyclic semisimplicial set with L²-acyclic simplex stabilizers has β_n^(2) = 0 for n <= m
distinct_from:
  l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup: that is vanishing forced by one infinite normal amenable subgroup of the group itself; this transfers vanishing from the stabilizers of an action on an acyclic complex, and applies to simple groups, which have no such normal subgroup.
---

**ESTABLISHED (proved on paper, unreviewed).** Let a countable group `G` act on a
semisimplicial set `X` so that the stabilizer `G_σ` of every simplex fixes it pointwise, and
suppose `H̃_d(X; Z) = 0` for `0 <= d <= m`. If `β_t^(2)(G_σ) = 0` whenever `σ` is a
`p`-simplex and `p + t <= m`, then `β_n^(2)(G) = 0` for `0 <= n <= m`.

It is Theorem D of `research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md`: the
stabilizer spectral sequence `E^1_(p,t) = ⊕ H_t(G_σ; N(G)) ==> H_(p+t)(G; N(G))`, valid in
total degrees `<= m`, has `E^1` terms of von Neumann dimension zero there.

Route: `l2-acyclic-stabilizers-spectral-sequence-proof`.
