---
rg: 2
id: higman-group-is-the-swap-twisted-double-of-a-bs-amalgam
kind: claim
title: Higman's group is the swap-twisted double of BS(1,2) *_Z BS(1,2) and has index two in a three-generator amalgam
artifacts:
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
---

Let `G_1 = <a,b,c | b^a = b^2, c^b = c^2>`, let `F = <a,c>` (free of rank two), and let `theta` be the swap
`a <-> c` of `F`. Then:

* Higman's group `H = <a,b,c,d | b^a=b^2, c^b=c^2, d^c=d^2, a^d=a^2>` is the twisted double `G_1 *_theta G_1`,
  which identifies `f` in one copy with `theta(f)` in the other;
* `alpha : a -> c, b -> d, c -> a, d -> b` is an order-two automorphism of `H`, and
  `E = H x|_alpha Z/2 = <a, b, t | t^2, b^a = b^2, (tat)^b = (tat)^2> = G_1 *_F (F x|_theta Z/2)`;
* `H` is surjunctive iff `E` is;
* the sign character `t -> -1` of `E` kills one of `(1 +- t)/2` in every odd characteristic, so averaging-idempotent
  corner witnesses do not exist over `E`.

So the extra room `E` offers over `H`, namely 2-torsion and its idempotents, adds no averaging-corner designs.

**The twist is essential.** The untwisted double `G_1 *_F G_1` is surjunctive
(`doubles-of-surjunctive-groups-are-surjunctive`). The swap extends to no endomorphism of `G_1`, because `a` and
`a^2` have different images in `G_1^ab = Z`. And `H` is not a double of `G_1` over any subgroup, since every such
double maps onto `Z` while `H` has no nontrivial finite quotient.

**ESTABLISHED 2026-09-12** by `higman-swap-twisted-double-proof`.
