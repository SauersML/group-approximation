---
rg: 2
id: products-with-lef-permanence-closure-factors-are-surjunctive
kind: claim
title: A surjunctive group times any group in the LEF permanence closure is surjunctive
distinct_from:
  products-with-lef-factors-preserve-surjunctivity: that is the LEF case; this closes the class of admissible second factors under subgroups, local embeddings, finitary split extensions and graph folds.
  finite-direct-products-of-surjunctive-groups-are-surjunctive: that is the unrestricted open product question; this proves the case where one factor lies in the LEF permanence closure.
artifacts:
  - research/artifacts/w3-products-permanence-closure-2026-09-12.md
---

Fix a surjunctive group `G` and put `P(G) = {K : G x K surjunctive}`. Then `P(G)`:
- contains every LEF group;
- is closed under subgroups and under local embeddings, hence under directed unions;
- contains `N ⋊ B` whenever that carries a finitary structure with base `B` in `P(G)`;
- contains `Q` whenever `Q` is the fundamental group of a connected graph of groups with injective edge
  maps admitting a homomorphism to a member of `P(G)` that is injective on vertex groups.

Consequences:
- **The closure.** The smallest class `Cl(LEF)` containing LEF groups and closed under these operations lies
  inside `P(G)` for every surjunctive `G`. It is closed under finite direct products.
- **Known witnesses.** For every surjunctive `G`, `G x W` and `G x D` are surjunctive, where `W` is a
  Kun–Thom wreath and `D` a Kun–Thom double. In particular `D x D` is surjunctive.
- **The open case.** The product question stays open only when both factors lie outside `Cl(LEF)`, which
  includes every group containing a finitely presented simple nonsofic FA subgroup
  (`sofic-permanence-closure-omits-simple-fa-nonsofic-groups`).

Proof: Section 2 of the artifact, route `lef-permanence-closure-product-surjunctivity-proof`.
