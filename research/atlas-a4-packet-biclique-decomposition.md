---
rg: 2
id: atlas-a4-packet-biclique-decomposition
kind: claim
title: The thirty A4 packet contexts reduce to K2,2 and K2,4 subgroup gadgets
artifacts:
  - experiments/atlas_a4_packet_component_audit.py
---

Identify the two `A8` chart alphabets by their common matrix labels and build
the undirected **pair graph** of the thirty shortest A4 contexts: an order-two
label `b` is joined to an order-three label `a` when one of the packet words is
`(b_2 a_1)^3` or its factor-reversed form.

Then the ten distinct packet labels split into exactly two connected
components.

1. The first component has two involution labels and two order-three labels.
   All four possible pairs occur, so its simple pair graph is `K_(2,2)`.  Its
   four labels generate a subgroup `H_6 < A8` of order `6`; the two
   involutions already generate all of `H_6`.
2. The second component has two involution labels and four order-three labels.
   All eight possible pairs occur, so its simple pair graph is `K_(2,4)`.  Its
   six labels generate a subgroup `H_18 < A8` of order `18`, with center of
   order `3`; its two involutions generate a subgroup of order `6`.
3. The two generated subgroups intersect trivially and together generate all
   of `A8`:

   ```text
   H_6 intersect H_18 = 1,
   <H_6,H_18> = A8.
   ```

Consequently

```text
H_6  ~= S3,
H_18 ~= S3 x C3.
```

At the level of distinct pair constraints, the thirty-word packet therefore
has only twelve edges and only four independent graph cycles: one rectangle in
`K_(2,2)` and three rectangles in `K_(2,4)`.

## Attempts

- The exact `F2` audit already computes the two connected components, subgroup
  orders, centers, involution-generated subgroup orders, trivial intersection,
  and the fact that their join has order `20160`.  What remains for this Cairn
  node is only the elementary group-theoretic interpretation and the biclique
  count, supplied by the proof route.
