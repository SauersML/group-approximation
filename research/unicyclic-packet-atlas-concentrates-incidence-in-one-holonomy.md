---
rg: 2
id: unicyclic-packet-atlas-concentrates-incidence-in-one-holonomy
kind: claim
title: A unicyclic packet atlas concentrates every exact incidence choice in one commutant holonomy
distinct_from:
  fanizza-native-additive-incidence-is-one-triangle: that computes the native context graph and its unique cycle; this is the representation-theoretic exact-amplification theorem for any such graph.
  closed-covariant-reynolds-cycle-has-full-overlap: that proves a finite covariant cycle cannot create a contracting Reynolds return; this only normalizes the exact completeness data and makes no finite-dimensional soundness claim.
---

Let a finite connected graph of finite packet groups have first Betti number
one.  At every vertex `v`, let `pi_v` be an exact packet representation, and
assume that on every edge the two endpoint restrictions have the same
irreducible support.  After countable amplification, all edge restrictions
have infinite multiplicity on precisely those types.

Choose a spanning tree.  Starting at a root, choose an exact unitary
intertwiner on every tree edge and transport the child vertex representation
through it.  Because the tree has no cycles, these choices are independent
and make every tree incidence exact.

There is one chord `e`.  The two endpoint restrictions on `e` are again
unitarily equivalent after amplification.  Relative to any one chosen
intertwiner `u_e`, every other choice is

```text
u_e h,       h in pi_e(H_e)',                          (UPA1)
```

where `H_e` is the edge packet.  Hence all exact incidence freedom not
removed by tree gauge is one unitary conjugacy class in the commutant of the
single chord separator.  Conversely every such `h` gives an exact completion.

Thus a unicyclic atlas has no distributed exact-completeness obstruction:

```text
tree incidences + one commutant holonomy.              (UPA2)
```

The proof is just induction along the spanning tree and the elementary fact
that two intertwiners between the same representations differ by a commutant
unitary.  Countable amplification turns equality of irreducible support into
unitary equivalence because every retained multiplicity is countably
infinite.

For the gauge-doubled native Fanizza incidence,
`fanizza-native-additive-incidence-is-one-triangle` supplies exactly this
graph: one leaf attached to one triangle.  Gauge-orbit covariantization makes
the separator supports match and fixes every retained logical word, so the
native signal remains nonzero throughout the tree normalization.  Exact
completeness is therefore reduced to choosing one chord-holonomy unitary;
properly infinite multiplicity is fully legitimate there.

This theorem does not give finite-dimensional soundness.  A finite
commutant holonomy may be nontrivial at zero relator defect, and
`closed-covariant-reynolds-cycle-has-full-overlap` rules out obtaining a
strict contraction from a finite covariant cycle alone.  A successful
compiler must charge that one holonomy by a non-covariant two-cell,
proper-corner return, or the native D8 moment obstruction.
