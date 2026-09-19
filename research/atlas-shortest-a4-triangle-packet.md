---
rg: 2
id: atlas-shortest-a4-triangle-packet
kind: claim
title: The first tensor-flip boundary contains thirty exact A4 triangle relations
artifacts:
  - experiments/atlas_triangle_19243_packet.py
---

In the complete radius-five spanning-tree kernel window for the two-chart
`A8*A8` Leavitt atlas, exactly thirty tree generators have all of the following
properties:

1. `X`-length exactly `9`, the sharp first possible boundary length;
2. free-product syllable length `6`;
3. the form

   ```text
   (b_2 a_1)^3
   ```

   or the factor-reversed form, with `ord(b)=2` and `ord(a)=3`.

Every one is therefore an exact `(2,3,3)` triangle relation.  In any exact
regular-character atlas realization, the two marginal operators have trace
zero, so `a4-triangle-zero-traces-force-regular` upgrades each relation from a
single word equation to a rigid local statement: the corresponding pair acts
as a direct sum of regular `A4` representations.

One explicit member is tree index `6910`, with factor-two involution

```text
01000000010100000000010000000001
```

and factor-one order-three element

```text
01010000010000000000010000000001.
```

Thus the first projection-bearing atlas boundary is not an unstructured list:
it contains a finite family of overlapping local `A4` representation charts.
