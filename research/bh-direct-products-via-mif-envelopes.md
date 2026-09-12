---
rg: 2
id: bh-direct-products-via-mif-envelopes
kind: route
title: Enlarge both envelopes to finitely presented simple MIF groups, pass to the permutational class, and take the product actor
target: boone-higman-closed-under-finite-direct-products
requires:
  - fp-simple-groups-embed-in-fp-simple-mif-groups
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Let `G <= S` and `H <= T`, with `S` and `T` finitely presented simple.
1. By `fp-simple-groups-embed-in-fp-simple-mif-groups`, `S <= M_1` and `T <= M_2`
   for finitely presented simple MIF groups `M_1` and `M_2`.
2. By BFFHZ Theorem C, imported as `fp-simple-highly-transitive-groups-satisfy-pbh`,
   every subgroup of a finitely presented simple MIF group lies in `B_A`. So `G`
   and `H` lie in `B_A`.
3. By `boone-higman-type-a-class-closed-under-finite-extensions`, `G x H` lies in
   `B_A`, and every member of `B_A` embeds in a finitely presented simple group.

So `G x H` embeds in a finitely presented simple group.
