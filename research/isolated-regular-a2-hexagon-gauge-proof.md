---
rg: 2
id: isolated-regular-a2-hexagon-gauge-proof
kind: route
title: Amplify one coherent packet and put an arbitrary unitary on one edge
target: isolated-regular-a2-hexagon-has-free-external-holonomy
requires: []
---

If the six packet restrictions agree literally on their edge subgroups,
the six identity operators are valid compatibility intertwiners and have
trivial product.  After tensoring every packet representation with `1_K`,
the full algebra `1_E tensor B(K)` commutes with every vertex and edge
action.  Multiplying the last edge intertwiner on its target side by
`1_E tensor Z` therefore preserves its intertwining equation and changes
the closed product from `1` to `1_E tensor Z`.  Multiplication by the inverse
undoes it.  This proves `(IRH2)--(IRH4)`.

For a finite overgroup `F`, its left regular representation restricts to
`[F:G]` copies of the left regular representation of every subgroup `G`:
decompose `F` into left `G`-cosets.  Taking `F=SL_3(F_q)` and its six ordered
unipotent radicals supplies the stated coherent regular `A_2` packet.
