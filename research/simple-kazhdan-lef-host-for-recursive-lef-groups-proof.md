---
rg: 2
id: simple-kazhdan-lef-host-for-recursive-lef-groups-proof
kind: route
title: Embed the restricted direct sum of the family, which is countable and LEF
target: simple-kazhdan-lef-host-for-recursive-lef-groups
requires:
  - countable-lef-groups-embed-in-simple-kazhdan-lef-groups
  - subshift-elementary-group-word-problem-degree
  - finitely-generated-linear-groups-are-residually-finite
artifacts:
  - research/artifacts/sk-universal-lef-host-b-2026-09-13.md
---

Artifact §3.

**(a)**
- `D = ⊕_(C ∈ 𝒞) C` is countable.
- `D` is LEF. A finite subset `A ⊆ D` lies in a finite product `C_1 × … × C_m`, and it projects to finite sets `A_i`.
  Products of partial models `C_i -> Q_i`, injective and multiplicative on the `A_i` together with their pairwise
  products, give a partial model of `A`.
- Every `C ∈ 𝒞` is a subgroup of `D`.
- By `countable-lef-groups-embed-in-simple-kazhdan-lef-groups`, `D ≤ U`.

**(b)**
- **Countability.** A recursively presented f.g. group is `⟨s_1,…,s_k | Rel⟩` with `Rel` recursively enumerable. There
  are countably many such presentations, so up to isomorphism the recursively presented f.g. LEF groups form a
  countable set, and (a) applies.
- **Examples.**
  - Finitely presented groups are recursively presented, and residually finite groups are LEF.
  - Finitely generated linear groups are residually finite (`finitely-generated-linear-groups-are-residually-finite`),
    and recursively presented through decidable ideal membership, as recorded (recalled, not re-read) in
    `universal-simple-kazhdan-lef-groups-exist-proof`.
  - For `Y` with recursive language, `WP(G_Y)` has the degree of `L(Y)` (`subshift-elementary-group-word-problem-degree`).
    So it is solvable, and a group with solvable word problem is recursively presented. `G_Y` is LEF by the note's
    Theorem 1. Examples: the Fibonacci subshift, and Sturmian `X_α` with computable irrational `α`. Only embedding is
    claimed; which of these groups are isomorphic is not addressed.
  - Derived topological full groups of minimal subshifts with recursive language: they are f.g. (Matui) and LEF
    (Grigorchuk–Medynets 2014), with decidable word problem (Grigorchuk–Medynets 2018, Thm 1.1(3)). These are recalled
    citations.
- **Scope.** The Matui and Grigorchuk–Medynets example is illustrative. The route requires only the three named claims.
  ∎
