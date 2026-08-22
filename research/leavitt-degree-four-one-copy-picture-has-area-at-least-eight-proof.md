---
rg: 2
id: leavitt-degree-four-one-copy-picture-has-area-at-least-eight-proof
kind: route
title: Test every area-six outer region for one exact Leavitt free-product syllable
target: leavitt-degree-four-one-copy-picture-has-area-at-least-eight
requires:
  - leavitt-degree-four-target-picture-has-area-at-least-six
---

The mixed-valence signed-ribbon census described in
`leavitt-degree-four-target-picture-has-area-at-least-eight-proof` was rerun
with the target filter removed.  A ribbon is accepted whenever all but one
coefficient region reduce to the identity and the remaining region has exact
free-product normal form

```text
(i,g),                 i in Z/4,  1 != g in G_i.     (OC1)
```

Thus `(OC1)` recognizes every nontrivial outer boundary contained in one full
coefficient copy, irrespective of its expression in the named packet
generators.

The area-six census was split into eight disjoint MSI shards by the index of
the relator-type multiset.  Their planar-ribbon counts were

```text
152220, 524588, 352648, 491432,
800752, 242868, 298316, 258856,
```

which sum to the independent unsharded total `3,121,680`.  Every shard
reported

```text
one_copy_disks=0 one_copy_units=0.
```

Together with the exact area-two/four result and the odd-area sign-balance
obstruction, this excludes every coefficient-kernel picture through area six
and proves the lower bound eight.
