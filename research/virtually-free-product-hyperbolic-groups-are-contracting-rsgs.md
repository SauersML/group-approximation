---
rg: 2
id: virtually-free-product-hyperbolic-groups-are-contracting-rsgs
kind: claim
title: Every non-elementary hyperbolic group with a finite-index subgroup that is a nontrivial free product, in particular every non-elementary virtually free group such as SL_2(Z), is isomorphic to a contracting rational similarity group
distinct_from:
  free-products-of-hyperbolic-groups-are-contracting-rsgs: that is the free products themselves; this passes to every finite-index overgroup, which covers groups with non-split finite radicals and splittings over nontrivial finite groups.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1; this settles every case with infinitely many ends, apart from groups with no finite-index subgroup that splits freely.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**ESTABLISHED** by `virtually-freely-decomposable-hyperbolic-rsg-proof` (lane `bh-free-23`,
lane proof, not independently reviewed; no priority claimed).

## Statement

Let `G` be a non-elementary hyperbolic group with a finite-index subgroup `K = A * B`, where `A`
and `B` are nontrivial. Then `G` is isomorphic to a contracting RSG.

## Instances

- **Every non-elementary virtually free group.** This includes `SL_2(Z)` (center `Z/2`, not a
  direct factor), `GL_2(Z)`, and every fundamental group of a finite graph of finite groups that
  is not virtually cyclic.
- **Every virtually torsion-free hyperbolic group with infinitely many ends.** A torsion-free
  finite-index subgroup has infinitely many ends, so by Stallings's theorem it is a nontrivial
  free product.
- **Every hyperbolic group commensurable with a free product of hyperbolic groups**, other than
  `Z/2 * Z/2`.
