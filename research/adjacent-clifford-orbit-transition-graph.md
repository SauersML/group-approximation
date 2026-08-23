---
rg: 2
id: adjacent-clifford-orbit-transition-graph
kind: claim
title: The adjacent dyadic Iwahori Clifford transition graph has one lossy recurrent orbit
distinct_from:
  fixed-clifford-sectors-have-zero-adjacent-opposite-overlap: that computes only the invariant-character source and proves its fixed-to-fixed overlap is zero; this gives every newest-layer orbit, its exact source-capacity weights, and the recurrent component.
  iwahori-dual-inclusion-graph-is-fusion-not-the-bruhat-tits-tree: that gives the one-level one-sided fusion components; this computes the directed overlay between consecutive upper and opposite levels.
  sparse-dyadic-iwahori-packets-have-a-uniform-boundary: that forgets Clifford labels and gives a universal two-thirds fixed-space ceiling; this identifies exactly which orbit attains that ceiling and where the remaining third goes.
---

Write the four `SL_2(F_2)`-orbits in the dual of the newest layer as

```text
O_0={(0,0,0)},
O_F={(1,1,1)},
O_A={(1,0,0),(1,0,1),(1,1,0)},
O_B={(0,1,0),(0,1,1),(0,0,1)}.                         (COT1)
```

For adjacent upper depth `a` to opposite depth `a+1`, the exact directed
orbit transitions, labelled by the maximal fraction of the source
representation which can participate, are

```text
O_0 -> O_0   [1],
O_F -> O_B   [1],
O_A -> O_0   [2/3],       O_A -> O_B   [1/3],
O_B -> O_0   [1/3],       O_B -> O_B   [2/3].           (COT2)
```

The reverse adjacent orientation (opposite depth `a` to upper depth
`a+1`) has the same orbit graph and weights. In `(COT2)`, `O_0` means that
the target factors through the preceding quotient; after restricting to
exact-conductor targets, the `O_0` arrows are deleted. Thus every nonzero
adjacent exact-conductor transition lands in `O_B`.

The inertia indices in `G_a` are

```text
[G_a:I(O_0)]=[G_a:I(O_F)]=1,
[G_a:I(O_A)]=[G_a:I(O_B)]=3.                            (COT3)
```

The root-coordinate-one weights responsible for exact upward transport are

```text
# {mu in O: beta_mu=1}/|O| = 0,1,1/3,2/3               (COT4)
```

for `O=O_0,O_F,O_A,O_B`, respectively, in the upper-to-opposite
orientation. In the reverse orientation `beta` is replaced by `gamma`, and
the four fractions are identical.

Consequently `O_B` is the unique recurrent nonzero orbit and it can
self-propagate at every depth, but at most a `2/3` fraction of its incoming
physical dimension can continue to the next exact conductor. With no fresh
input from another orbit, mass surviving `k` consecutive adjacent steps is
at most `(2/3)^k`. The full-inertia orbit `O_F` feeds `O_B` once with weight
one but has no incoming nonzero arrow; `O_A` feeds it with only weight
`1/3`. Hence no single newest-layer orbit, including `O_B`, realizes the
asymptotically lossless diffuse scalar flow. Any realization must use
additional within-inertia multiplicity transport and repeated cross-orbit
replenishment not visible in a one-way adjacent chain.

