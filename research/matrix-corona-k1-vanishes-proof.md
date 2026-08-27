---
rg: 2
id: matrix-corona-k1-vanishes-proof
kind: route
title: Six-term sequence for the matrix corona extension
target: matrix-corona-k1-vanishes
requires: [matrix-corona-product-k0-is-rank-bounded-sequences]
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

`K_0(oplus_n M_{d_n}) = oplus_n Z`, by coordinatewise rank together with the
fact that a norm-null sequence of projections has finitely many nonzero
coordinates, a nonzero projection having norm one.

For the product, **corrected 2026-08-17**: this route previously asserted
`K_0(prod_n M_{d_n}) = prod_n Z`, which is false.  A single stabilization
size `k` must serve every coordinate, so the realizable rank sequences are
those with `sup_n r_n/d_n < oo` and

    K_0(prod_n M_{d_n}) = L(d) = { (z_n) : sup_n |z_n|/d_n < oo },

by `matrix-corona-product-k0-is-rank-bounded-sequences`.  Nothing here
depends on which of the two it is: the step this route needs is injectivity
of `K_0(oplus) -> K_0(prod)`, and that map is the inclusion
`oplus_n Z <= L(d)` -- a finitely supported sequence is trivially
rank-bounded -- which is injective either way.

Exactness at `K_1(Q)` makes the index map injective, and exactness at
`K_0(oplus)` identifies its image with the kernel of an injective map,
hence `K_1(Q) = 0`.
