---
rg: 2
id: atlas-a4-19243-s3xs3-localization
kind: claim
title: Collision 19243 is supported on the S3 factor of the large packet component and one commuting S3 partner
artifacts:
  - experiments/atlas_a4_19243_component_localization.py
  - experiments/atlas_19243_s3_relative.py
---

Let `H_18 ~= S3 x C3` be the six-label component of the shortest A4 packet
from `atlas-a4-packet-biclique-decomposition`, and write

```text
Z = Z(H_18) ~= C3.
```

Let `x_1,x_2,x_3,x_4` be, in order, the four second-chart syllables of
collision `q_19243`, and let `b` be its repeated first-chart involution.  Then

```text
K = <x_1,x_2,x_3,x_4> ~= S3,
H_18 = K x Z.                                         (19243-CELL-1)
```

More precisely the four orders are

```text
3,2,3,2,
```

all four syllables lie in `H_18`, none lies in the other packet component
`H_6`, and they generate exactly the involution-generated `S3` direct factor
of `H_18`.

The first-chart involution `b` centralizes `K` and conjugates every nontrivial
`z in Z` to `z^-1`.  Hence

```text
L = <Z,b> ~= S3,
<K,L> = K x L ~= S3 x S3,                              (19243-CELL-2)
```

and this product has order `36`.  Equivalently

```text
<H_18,b> ~= S3 x S3.
```

Thus the collision does **not** probe an arbitrary part of `A8`: together with
the large biclique component it closes inside one fixed `S3 x S3` transport
cell.  In the already-established classical relative normal form its equation
is therefore the four-alternation

```text
r c s c r^-1 c (s r) c = 1,
```

with `r,s` generating the first `S3` and `c` an involution from the commuting
partner.  This is the smallest finite representation category in which to
analyze how collision `19243` frustrates the large packet component.
