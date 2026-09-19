---
rg: 2
id: atlas-six-relator-l44-subfield-has-no-marked-pair
kind: claim
title: The standard subfield A8 in L4(4) has no six-relator marked partner
artifacts:
  - experiments/atlas_l44_six_relator_screens.py
  - experiments/atlas-six-relator-l44-subfield-screens.json
distinct_from:
  atlas-l44-subfield-packet-collision-exclusion: that imposes the full cross-A4 packet and collision; this uses only the five saturated boundary words and c_19243.
  atlas-six-relator-simple-index-is-at-least-48960: that identifies L4(4) as the equality overgroup but does not classify or screen its A8 embeddings; this screens only the standard subfield class and deliberately does not claim the next index bound.
---

**ESTABLISHED.**  Fix the standard subfield chart

```text
A=GL4(2)~=A8 < PSL4(4)=L4(4).
```

For both relative markings of a second conjugate subfield chart `B`--the
inner marking and the graph marking `g |-> (g^-1)^T`--there is no relative
conjugator satisfying

```text
s_0=s_11=s_30=s_44=s_55=c_19243=1.                   (S6L44-1)
```

In either parity, `s_0` has `30` hits in its `5355`-element involution class.
The projective seed centralizer has size `184320`, giving exactly `5529600`
relative conjugators per parity.  Their first-failure census is

```text
marking   s_11       s_30   s_44   s_55   c_19243   survive
inner     5528592    864    108    27     9         0
graph     5529600    0      0      0      0         0.       (S6L44-2)
```

This removes the advertised standard subfield equality chart.  The companion
classification `atlas-l44-has-one-a8-class-with-self-normalizer` now proves
that every abstract `A8<L4(4)` is conjugate to this chart, its normalizer is
itself, and the two cases above are exactly all unabsorbed marking parities.
Thus the composite claim `atlas-six-relator-l44-has-no-marked-pair` exhausts
the equality endpoint.

## Completed Atlas classification

The characteristic-two Brauer table has exactly two degree-four irreducibles,
dual to one another.  Both realize the same subgroup image `GL4(2)`, while
the exact projective normalizer has order `20160`.  There are no further
subgroup classes or cross-class pair screens.
