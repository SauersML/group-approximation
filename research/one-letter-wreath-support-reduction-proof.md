---
rg: 2
id: one-letter-wreath-support-reduction-proof
kind: route
title: Exhaust by conjugates of B x| Gamma and quotient by a cyclic group
target: one-letter-wreath-support-reduces-to-gamma-orbit-wreaths
requires:
  - sofic-kernel-amenable-quotient-permanence
---

1. From `t Gamma t^(-1) <= Gamma`, the groups `t^(-k) Gamma t^k` increase,
   so `N = union_k t^(-k) Gamma t^k` is normal in `G_t` and `G_t/N` is
   cyclic.
2. `B x| N` is the increasing union of the conjugates
   `t^(-k) (B x| Gamma) t^k`. Soficity is decided on finitely generated
   subgroups, so `B x| N` is sofic if `B x| Gamma` is.
3. `B x| N` is normal in `B x| G_t` with cyclic quotient, so the permanence
   theorem finishes item 1.
4. For item 2, a finitely generated subgroup of `B x| Gamma` meets finitely
   many orbits and embeds diagonally in the product of those orbit wreaths.
   Each orbit wreath is also a subgroup of `B x| Gamma`.
