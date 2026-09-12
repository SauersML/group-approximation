---
rg: 2
id: atlas-a8-hall-deficit-needs-439-forbidden-blocks
kind: claim
title: A regular-A8 Fourier Hall deficit requires at least 439 forbidden block pairs
distinct_from:
  atlas-a8-mixed-block-transport-has-permutation-models: that realizes every rational block-mass transport and computes the Hall-gap mesh; this computes the sharp support-deletion complexity of any deficient graph.
  regular-subgroup-branching-is-hall-balanced: that proves one natural restriction incidence graph is balanced; this treats every possible graph on the 448 minimal regular-A8 Fourier vertices.
  atlas-wedderburn-hall-deficient-support-certificate: that asks the relators to force some deficient graph; this proves that such a graph must coordinate at least 439 whole-block deletions and that this bound is sharp.
---

**ESTABLISHED SHARP COMBINATORIAL FIREWALL.**  Give each of the 448 minimal
regular-`A8` Fourier vertices its integer numerator weight `d_sigma`, so the
total weight on either side is `20160`.  For any bipartite allowed-edge graph
`E`, if a source set `S` has strict Hall deficit

```text
w(S)>w(N_E(S)),                                       (H439-1)
```

then at least

```text
439                                                     (H439-2)
```

source--target block pairs are absent from `E`.

The bound is sharp.  Choose one source vertex of weight `70`.  Let its
neighborhood consist of nine target vertices: the unique weight-`1` vertex,
all seven weight-`7` vertices, and one weight-`14` vertex.  This neighborhood
has total weight

```text
1+7*7+14=64<70.                                      (H439-3)
```

Delete exactly the other `448-9=439` edges incident to that source and retain
all remaining graph edges.  Then `(H439-1)` holds.

Equivalently, every prescription of at most 438 forbidden whole-block pairs
has an exact finite absorber.  Its allowed graph satisfies all weighted Hall
inequalities, so integral max-flow gives a table with margins `d_v,d_u`
supported on the allowed edges.  The permutation construction of
`atlas-a8-mixed-block-transport-has-permutation-models` then gives

```text
U in U(20160),          q_u U p_v=0                  (H439-6)
```

on every prescribed forbidden pair.  No amplification is required.

Consequently no single mixed minor, one compressed block, or any collection
which only proves at most 438 individual whole-block vanishings can establish
`atlas-wedderburn-hall-deficient-support-certificate`.  A successful hard
support proof must make one relation-sensitive implication delete a large
coordinated family of Fourier pairs, or it must work at the finer
within-block range level where one common kernel can simultaneously reduce
many target ranges without declaring whole blocks zero.

This does not rule out a small *algebraic* minor whose nonvanishing controls
hundreds of block restrictions at once.  It specifies exactly what such a
minor must achieve and prevents interpreting one local kernel calculation as
a Hall certificate without auditing its full 439-edge orbit.
