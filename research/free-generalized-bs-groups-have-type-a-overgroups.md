---
rg: 2
id: free-generalized-bs-groups-have-type-a-overgroups
kind: claim
title: Every generalized Baumslag--Solitar group over a non-abelian free group embeds in a finitely presented group with a type (A) action
distinct_from:
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports the Bux--Llosa Isenrich--Wu embeddings into finitely presented simple groups; this imports their stronger permutational form for the class over free groups, which puts those groups in the class that is closed under finite-index overgroups.
  permutational-boone-higman-conjecture: that is the open universality conjecture; this is one class for which the permutational property is known.
  boone-higman-type-a-class-closed-under-finite-extensions: that is the permanence of the type (A) class; this supplies members of that class.
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

**ESTABLISHED (literature import).** For `k >= 2` let `BS_(F_k)` be the class
of fundamental groups of finite graphs of groups whose vertex and edge groups are
abstractly commensurable with `F_k`, with all edge inclusions of finite index.
Every group in `BS_(F_k)` embeds in a finitely presented group admitting an
action of type (A), as defined in
`type-a-action-gives-boone-higman-for-subgroups`.

Source: K.-U. Bux, C. Llosa Isenrich, X. Wu, arXiv:2408.05673v2, extracted on
MSI (`/scratch.global/sauer354/orbh-lit/2408.05673.txt`).
- **Remark 12.7, verbatim:** "Our proof of Theorem 12.5 shows that for every
  group in BS_{F_k} the permutational Boone–Higman Conjecture holds, that is,
  every such group embeds in a finitely presented group that admits an action of
  type (A) on a countable set in the sense of Zaremsky [Zar24a, Conjecture 5.1]."
- **The definition of `BS_G`,** §11: "the class of groups consisting of all
  (finite) graphs of groups with the property that all edge and vertex groups are
  abstractly commensurable with G and all edge group inclusions in vertex groups
  have finite index".

**Members.** Every finitely generated free-by-cyclic group `F_k ⋊ Z` with
`k >= 2` belongs: it is an HNN extension of `F_k` along an automorphism.
Burger--Mozes groups belong too (their Theorem 12.6).

Not reproved here, and there is no Lean counterpart.
