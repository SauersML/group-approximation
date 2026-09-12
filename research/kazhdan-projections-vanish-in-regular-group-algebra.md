---
rg: 2
id: kazhdan-projections-vanish-in-regular-group-algebra
kind: claim
title: The Kazhdan projection of an infinite subgroup is zero in the group von Neumann algebra and is not a group-ring element
invalidates:
  - wreath-atom-via-kazhdan-projection-conjugation
---

**ESTABLISHED.** Let `Lambda` be an infinite subgroup of `W`. In `L(W)`
acting on `l^2(W)`, the projection onto `Lambda`-invariant vectors is `0`: an
invariant vector is constant on the infinite cosets `Lambda w`, so it is not
square-summable. So conjugating by a Kazhdan projection produces the zero
operator in the trace picture, and that projection is not in `Z[W]` anyway.

What property (T) of `Lambda` does give is a spectral gap: the Laplacian
`sum_(s in S)(2 - u_s - u_s^*)` over a Kazhdan generating set is invertible on
`l^2(W)`, so its spectral measure has no atom at `0`.
