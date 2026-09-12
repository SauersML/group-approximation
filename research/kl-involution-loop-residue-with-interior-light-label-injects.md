---
rg: 2
id: kl-involution-loop-residue-with-interior-light-label-injects
kind: claim
title: The length-six residue shapes (1,1,g,1) and (1,g,1,1) with involution loops inject when g avoids four short relations with the loops
distinct_from:
  kl-three-coincidence-residue-words-inject-with-room-for-loops: that uses a weight test, which needs 2/k_y + 2/k_x <= 1 and so excludes involution loops; this handles involution loops by moving the positive curvature of the loop-square regions onto neighbouring regions.
  kl-length-six-residue-squares-and-fourth-powers-inject: that settles (1,1,g,1) with g = y and (1,g,1,1) with g = x for every loop order, by substitution; this settles the same two shapes with involution loops for every g outside four short relations.
  kl-length-six-coincidence-saturated-torsion-residue: that is the open statement for all residue shapes; this proves two of its eight +++++- shapes in the involution-loop case of the Leavitt search, under generic conditions on g.
---

Let `G` be any group, and `x, y in G` involutions (`x^2 = y^2 = 1`, `x, y != 1`).
Let `g in G`, `g != 1`, and

```text
w = t a_1 t a_2 t a_3 t a_4 t y t^(-1) x,     (a_1,a_2,a_3,a_4) = (1,1,g,1) or (1,g,1,1).
```

Suppose:
- (I1) `g` is neither `x` nor `y`;
- (I2) `g x g^(-1) != y`;
- (I3) `g != y x`;
- (I4) `g^2 x g^(-1) y != 1`.

Then `G -> (G * <t>)/<<w>>` is injective, and every reduced spherical picture over
`<G, t | w>` is empty.

These are the normalized residue shapes of
`kl-length-six-coincidence-saturated-torsion-residue` whose light P-label sits at
an interior position of the positive run, not next to a sign change. There the
relative weight test is impossible, because the heavy triple and two involution
loops need weight five against a budget of four.

**Method.** Weight the heavy triple by `1`, the light corner by `0`, and both
loops by `1/2`. The only admissible regions of weight below two are the loop
squares `y^2` and `x^2`, each of curvature `pi`. Each loop square hands `pi/2`
across each of its two arcs. In these two shapes every receiving region gains a
distinct heavy corner and a distinct loop corner per transfer, and (I3)-(I4)
remove the receivers that could not absorb it.

**Not covered.**
- `(1,1,1,g)` and `(g,1,1,1)`: one of the two loop squares hands its curvature
  to a region through the light corner, and the count fails.
- The two-pair shapes, and every `++++--` shape: there the receiving arcs join two
  same-sign corners and no loop corner.
- Loops of order two and three, or other small orders with
  `2/k_y + 2/k_x > 1`.

DERIVATION
kl-involution-loop-interior-light-label-curvature-proof
