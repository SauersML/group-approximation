---
rg: 2
id: fp-metabelian-bh-via-linear-factors-and-products
kind: route
title: Split a metabelian group into linear quotients of pure characteristic, envelope each, and take the product
target: fp-metabelian-groups-satisfy-boone-higman
requires:
  - fg-metabelian-groups-embed-in-products-of-coprimary-quotients
  - char-zero-linear-groups-satisfy-boone-higman
  - positive-char-linear-groups-satisfy-boone-higman
  - boone-higman-closed-under-finite-direct-products
---

Let `G` be a finitely presented metabelian group. It is finitely generated.

1. **Linear pieces.** By `fg-metabelian-groups-embed-in-products-of-coprimary-quotients`,
   `G` embeds in `G_0 x G_(p_1) x ... x G_(p_s)`. The primes are distinct, and
   each `G_c` is a finitely generated quotient of `G` that is linear over a field
   of characteristic `c`.
2. **Envelopes.**
   - `G_0` embeds in a finitely presented simple group by
     `char-zero-linear-groups-satisfy-boone-higman`.
   - Each `G_(p_j)` does by `positive-char-linear-groups-satisfy-boone-higman`.
3. **Product.** Applying `boone-higman-closed-under-finite-direct-products`
   `s` times embeds the product in a finitely presented simple group, and `G` is
   a subgroup of it.

**What this route over-asks.** Steps 2 and 3 need only metabelian factors and
products of them. The general linear roots are required because they are the
nodes the graph already carries.
