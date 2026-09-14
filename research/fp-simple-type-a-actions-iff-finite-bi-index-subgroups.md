---
rg: 2
id: fp-simple-type-a-actions-iff-finite-bi-index-subgroups
kind: claim
title: A finitely presented simple group has an action of type (A) exactly when it has a proper finitely generated subgroup with finitely many double cosets
distinct_from:
  simple-core-bi-index-counts-coset-action-pair-orbits: that counts pair-orbits of the coset action of an envelope on its normally generating simple core; this is about a finitely presented simple group acting on the cosets of its own subgroups, and adds the converse, that every type (A) action of such a group comes from one.
  two-transitive-action-reduces-type-a-to-two-clauses: that makes the pair clause free under 2-transitivity; this characterizes, for simple groups, which subgroups give type (A) coset actions, and 2-transitivity is the case of two double cosets.
  finite-bi-index-subgroups-have-decidable-membership: that decides membership in a subgroup with finitely many double cosets; this turns such a subgroup of a finitely presented simple group into a type (A) action.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4 for all finitely presented simple groups; this answers it positively for every finitely presented simple group carrying a finitely generated subgroup of finite bi-index.
artifacts:
  - research/artifacts/type-a-invariants-2026-09-13.md
---

**ESTABLISHED** through `fp-simple-type-a-iff-finite-bi-index-proof`. Not
independently reviewed. Elementary; no novelty claimed.

## Statement

Let `S` be a nontrivial finitely presented simple group. The following are
equivalent.

1. `S` admits an action of type (A) (four clauses, as quoted from Zaremsky in
   `type-a-action-gives-boone-higman-for-subgroups`).
2. `S` has a proper finitely generated subgroup `H` with `|H \ S / H| < infinity`.

When they hold, the action in (1) can be taken to be `S` acting on `S/H`. Then
`S` satisfies permutational Boone--Higman by definition, and by BFFHZ Theorem C
(`fp-simple-highly-transitive-groups-satisfy-pbh`, (i) ⟹ (iv)) `S` embeds in a
finitely presented simple MIF group. So BFFHZ Question 3.4 holds for `S`.

## What this adds

- **A one-subgroup test.** For simple groups the four type (A) clauses reduce to
  one arithmetic condition on one finitely generated subgroup. Faithfulness is
  free, because the normal core of a proper subgroup of a simple group is trivial.
- **The converse.** A type (A) action of `S` is never needed beyond a single orbit.
  Any orbit with at least two points gives such a subgroup. So "S has no type (A)
  action" and "every proper finitely generated subgroup of S has infinitely many
  double cosets" are the same statement.
- **Instances already on main.** A 2-transitive action has two double cosets.
  Examples are the Chen-module line actions of the Leavitt unit groups modulo
  scalars (`leavitt-units-act-two-transitively-on-chen-module-lines`) and of the
  tensor-square Leavitt unit groups
  (`leavitt-square-units-act-two-transitively-on-chen-lines`).
- **Not a separation.** Failing (2) does not refute permutational Boone--Higman for
  `S`, since `S` may still embed in a larger actor. See
  `q34-counterexample-necessary-conditions`.
