---
rg: 2
id: jacobson-recursive-affine-cells-do-not-force-boundary
kind: claim
title: The recursive affine equations and enlarged finite packets do not imply the boundary relation
distinct_from:
  jacobson-full-boundary-forces-six-coordinate-packet: that reconstructs the exact six-coordinate packet from Theta's full relations; this gives a finite countermodel to using a specified subset of its recursive consequences to infer the next boundary relation.
artifacts:
  - research/artifacts/jacobson-recursive-affine-cell-countermodel-2026-09-08.md
---

There is a finite group with an embedded packet

```text
K x R ~= GL_6(F_2) x GL_3(F_2),
```

and involutions `h,u` satisfying the following exact conditions.
Let `C_0=GL_5(F_2)<=K` be the standard subgroup fixing the sixth
coordinate, let `V=(F_2^5)^*`, let `a_v` be the row transvection
from that five-coordinate source space to the sixth coordinate,
and let `r=x_23` in `R`. Then

```text
[h,C_0]=[u,C_0]=1,             (hu)^3=1,
[u,h(a_v r)h]=a_v r            for every v in V,
[u,h a_v h]a_v != 1            for every nonzero v in V.
```

In particular the product-cell identity holds for all 31 nonzero
row roots, and even for the extra zero-vector case. The residual
element `r` centralizes the whole `K`, and the head packet is
faithfully represented. Nevertheless every nonzero boundary defect
survives. The two families `a_v r` and `h(a_v r)h` are each
commuting families of involutions.

This rules out deriving the recursive boundary relation from precisely
these equations and finite packets. It establishes no independence
from Theta's full relations. In this finite countermodel neither
the identification `u=[h delta(c)h,delta(k)]` and its full shifted
`GL_3` packet nor the first braid involving
`tau(q_P)delta(q_P)` is asserted. It therefore refutes neither
Theta's marked matrix-gap conjecture nor the non-MF goal.

DERIVATION
jacobson-vector-valued-quadratic-affine-countermodel-proof
