---
rg: 2
id: fp-metabelian-bh-via-quasi-linear-pbh
kind: route
title: Split a metabelian group into linear quotients of pure characteristic and place the product in B_A through self-similar hosts
target: fp-metabelian-groups-satisfy-boone-higman
requires:
  - fg-metabelian-groups-embed-in-products-of-coprimary-quotients
  - quasi-linear-groups-satisfy-permutational-boone-higman
artifacts:
  - research/artifacts/bh-quasi-linear-pbh-2026-09-13.md
---

Direct proof (2026-09-13, lane `bh-metabelian`). Not independently reviewed.

Let `G` be a finitely presented metabelian group. It is finitely generated.

1. **Linear pieces.** By
   `fg-metabelian-groups-embed-in-products-of-coprimary-quotients` (Wehrfritz 1975,
   Corollary 1.2, with a direct primary-decomposition proof), `G` embeds in
   `G_0 x G_(p_1) x ... x G_(p_s)`. Each `G_c` is a quotient of `G` that is linear
   over a field of characteristic `c`.
2. **Quasi-linear.** So `G` embeds in a finite product of general linear groups
   over fields. By `quasi-linear-groups-satisfy-permutational-boone-higman`, `G` is
   in `B_A`, and so embeds in a finitely presented simple group. ∎

**Compared with `fp-metabelian-bh-via-linear-factors-and-products`.** That route
needs `boone-higman-closed-under-finite-direct-products`, because its envelopes
in positive characteristic are Leavitt hosts not known to lie in `B_A`. Here every
factor, in every characteristic, sits inside a finitely presented self-similar
group, so the product step happens inside `B_A`.

**Stronger conclusion.** The argument gives membership in `B_A`: every finitely
generated metabelian group satisfies the permutational Boone--Higman conjecture of
BFFHZ, arXiv:2503.21882v2.
