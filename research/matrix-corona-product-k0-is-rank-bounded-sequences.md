---
rg: 2
id: matrix-corona-product-k0-is-rank-bounded-sequences
kind: claim
title: K-zero of the bounded matrix product is the rank-bounded sequences, not the full product
distinct_from:
  matrix-corona-k0-index-survives: that computes K_0 of the corona quotient Q and reads off that relative indices survive; this computes K_0 of the bounded product A upstream of the quotient, and is the step that node had wrong.
  matrix-corona-k1-vanishes: that is the K_1 statement for the quotient; this is a K_0 statement for the product, and is one of its inputs.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

For a sequence `(d_n)` of positive integers write `A = prod_n M_{d_n}` for
the bounded (`ell^infinity`) product and

    L(d) = { (z_n) in prod_n Z : sup_n |z_n| / d_n < oo }.

Then

    K_0(A) = L(d),        **not**  prod_n Z,

and `K_1(A) = 0`.

## The step that is easy to get wrong

A projection in `M_k(A) = prod_n M_{k d_n}` is a sequence of projections, and
Murray--von Neumann classes are read coordinatewise by rank -- that much is
standard, and the intertwiners assemble coordinatewise because a partial
isometry has norm one.  The trap is the stabilization bound: **one `k` must
serve the whole sequence**, so the realizable rank sequences are exactly
those with `r_n <= k d_n` for a single `k`, and the Grothendieck group is the
rank-bounded sequences `L(d)`, not all of `prod_n Z`.  For `d_n = 1` the
difference is stark: `K_0(A)` is the *bounded* integer sequences.  An integer
sequence growing faster than `d_n` is not represented at any finite
stabilization size.

## Why it matters here, twice

*It repairs two established nodes.*  `matrix-corona-k1-vanishes-proof` used
`K_0(prod) = prod Z` as an intermediate step and
`matrix-corona-k0-index-survives` carried `K_0(Q) = prod Z / (+) Z` in its
statement.  Both are corrected against this node.  Neither conclusion
changes: `K_1(Q) = 0` needs only injectivity of `(+)_n Z -> K_0(A)`, and
finitely supported sequences are trivially rank-bounded.

*It sharpens the surviving index.*  `K_0(Q) = L(d) / (+)_n Z` is the right
receptacle for the Exel--Loring / Bott index of an almost-commuting pair,
because such an index in `M_{d_n}` is a difference of ranks in `M_{d_n}` and
so is bounded by `d_n` on the nose.  The invariant lands in `L(d)`
automatically; it never needed the larger group, and the larger group was
never there.
