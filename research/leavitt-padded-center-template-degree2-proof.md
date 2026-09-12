---
rg: 2
id: leavitt-padded-center-template-degree2-proof
kind: route
title: Substitute every shortest unary orbit in faithful Bergman normal form
target: leavitt-padded-center-template-has-no-degree2-packet
requires:
  - leavitt-direct-tail-transport-screen-is-empty
  - leavitt-degree-four-target-picture-has-area-at-least-eight
---

## Abstract incidence hit

After a unary corner `X` gives `X=z^(-1)`, the signed nine-corner relator

```text
signs   (-,+,-,+,-,+,-,+,+)
corners (1,c,1,d,1,c,1,d,X)
```

reduces literally to

```text
z^-1 z c z^-1 z d z^-1 z c z^-1 z d z X = c d c d=[c,d].
```

The exact abstract screen tests 476,280 arrangements of the multiset
`(c,c,d,d,1,1,1,1,X)` and finds 416 cyclic variants of this identity.  Thus
the move from trivalent transport to a coupled higher-valence relation is a
real algebraic improvement, not another empty incidence ansatz.

## Shortest cyclic topology

The topology screen finds the first unary-plus-nine split at degree two,
length ten.  One representative sign word is

```text
(-,+,-,+,-,+,-,+,+,+).
```

Its two orbit valences are nine and one, and the nine orbit has precisely the
signed sequence displayed above.  Hence the abstract template is compatible
with Reidemeister--Schreier incidence.

## Exact full-packet obstruction

For each of the ten shortest sign topologies, the final artifact enumerates
all `10!/3!=604800` placements of

```text
(r,e,a,c,1,b,d,p,1,1).
```

It solves the unary orbit literally for `z`, substitutes that free-product
word for every `z^+-1` in the nine-valent orbit, and reduces in the faithful
twenty-leaf Bergman model of the two coefficient copies.  It accepts only the
exact central involution `[c_i,d_i]^+-1` in one copy.

MSI array job `16656531` completed all ten shards successfully.  Every shard
reports

```text
tested 604800
hits 0.
```

This is 6,048,000 exact layouts.  The screen is bounded: it excludes the
shortest degree-two full-packet realization, not degree three, longer packets,
or presentations in which a second non-unary orbit participates in killing
the center.
