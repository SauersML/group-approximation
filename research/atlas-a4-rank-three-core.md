---
rg: 2
id: atlas-a4-rank-three-core
kind: claim
title: Fourteen A4 packet words already form two S3 bicliques generating the standard GL3(2) core
artifacts:
  - experiments/atlas_a4_rank_three_core.py
---

Let `H_18=K x Z` be the large packet component from
`atlas-a4-19243-s3xs3-localization`, with `K ~= S3` and `Z ~= C3`.  Delete from
the thirty shortest A4 pair-cubes every word whose order-three packet label is
one of the two nonidentity elements of `Z`.

Exactly **fourteen** packet words remain.  Their distinct pair graph is

```text
K_(2,2) disjoint_union K_(2,2),                         (A4-CORE-GRAPH)
```

with seven word occurrences in each component.  The two component subgroups
are exactly

```text
H_6 ~= S3,
K   ~= S3,
```

and together they generate the standard rank-three subgroup

```text
H=<H_6,K>=diag(GL_3(F2),1),   |H|=168.                  (A4-CORE-H)
```

The discarded sixteen words are precisely those using the central `C3`
directions of `H_18`.

The classical automorphism audit becomes strictly sharper as well.  In each of
the inner and outer automorphism cosets of `Aut(A8)`, the fourteen-word core
has exactly the **same thirty surviving alignments** as the full thirty-word
packet.  Adding collision `q_19243` kills all thirty of those core survivors:

```text
core survivors                 = 30 inner + 30 outer,
full-packet survivors          = 30 inner + 30 outer,
core plus q_19243 survivors    = 0,
full packet plus q_19243       = 0.                      (A4-CORE-CLASSICAL)
```

Thus the central `C3` half of the large packet contributes no additional
filtering anywhere in the classical automorphism sector.  More importantly for
the nonhyperlinear route, the two named raw `S3` covariance directions already
live in this same rank-three `H`; forcing the relative chart frame into
`lambda(H)'` would therefore suffice.  Full `A8` packet-centrality is stronger
than necessary for the shortest contradiction.
