---
rg: 2
id: fp-simple-highly-transitive-groups-satisfy-pbh
kind: claim
title: A group satisfies permutational Boone--Higman exactly when it embeds in a finitely presented simple highly transitive, or MIF, group
distinct_from:
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4, whether every finitely presented simple group has a finitely presented simple MIF overgroup; this is their Theorem C, the equivalence that makes such an overgroup useful.
  aut-free-groups-satisfy-permutational-boone-higman: that imports Theorem A, together with Corollaries D and F; this imports Theorem C, the characterization of the permutational class by highly transitive and MIF envelopes.
  boone-higman-implies-relative-permutational-bh: that is FFWZ Theorem C, a relative permutational form with a possibly non-faithful action for every Boone--Higman group; this is BFFHZ Theorem C, the faithful permutational form for groups with highly transitive or MIF envelopes.
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

**ESTABLISHED (literature import).**

> **Theorem C (Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2).**
> "For a finitely generated group G (with solvable word problem) the following
> are equivalent:
> (i) G satisfies the permutational Boone–Higman conjecture, i.e., it embeds in
> a group admitting an action of type (A).
> (ii) G embeds in a finitely presented (simple) twisted Brin–Thompson group.
> (iii) G embeds in a finitely presented simple group that is highly transitive.
> (iv) G embeds in a finitely presented simple group that is MIF.
> In particular, every finitely presented simple group that is highly transitive,
> or more generally MIF, satisfies the permutational Boone–Higman conjecture, as
> does every subgroup thereof."

Their definition: "A group G is highly transitive if it admits a faithful action
on a set that is k-transitive for every k ≥ 1."

**As used here.** Every subgroup, finitely generated or not, of a finitely
presented simple group that is highly transitive or MIF lies in `B_A`, the class
of `boone-higman-type-a-class-closed-under-finite-extensions`. The proof of
(iv) ⟹ (i) embeds the simple group itself in `Aut_G(G * F_2)`, which carries a
type (A) action (their Theorem E).

**Use in this graph.** Parts (iii) ⟹ (i) and (iv) ⟹ (i) turn highly transitive
or MIF finitely presented simple envelopes into membership in `B_A`, which is
closed under direct products. Consumers:
- `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, through the
  highly transitive Rover--Nekrashevych envelopes;
- `bh-direct-products-via-mif-envelopes`, conditionally on
  `fp-simple-groups-embed-in-fp-simple-mif-groups`.
