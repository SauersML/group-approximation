---
rg: 2
id: matrix-corona-k1-vanishes-proof
kind: route
title: Six-term sequence for the matrix corona extension
target: matrix-corona-k1-vanishes
requires: []
---

## Why sufficient

Apply the six-term exact sequence to
`0 -> oplus M_{d_n} -> prod M_{d_n} -> Q -> 0`:

    K_1(prod) -> K_1(Q) -> K_0(oplus) -> K_0(prod).

`prod_n M_{d_n}` is a von Neumann algebra, and so is each matrix
amplification `M_k(prod_n M_{d_n}) = prod_n M_{k d_n}`; every unitary in a
von Neumann algebra is `exp(i h)` for a self-adjoint `h` by Borel
functional calculus, so all these unitary groups are norm-connected and
`K_1(prod) = 0`.

`K_0(oplus_n M_{d_n}) = oplus_n Z` and `K_0(prod_n M_{d_n}) = prod_n Z`,
both by coordinatewise rank: a projection in the product is a sequence of
projections, and two such are Murray--von Neumann equivalent exactly when
their ranks agree coordinatewise, the intertwining partial isometries being
assembled coordinatewise with norm one.  Under these identifications the
map `K_0(oplus) -> K_0(prod)` is the inclusion `oplus Z <= prod Z`, which is
injective.

Exactness at `K_1(Q)` makes the index map injective, and exactness at
`K_0(oplus)` identifies its image with the kernel of an injective map,
hence `K_1(Q) = 0`.
