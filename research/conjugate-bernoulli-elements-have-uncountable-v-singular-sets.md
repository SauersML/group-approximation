---
rg: 2
id: conjugate-bernoulli-elements-have-uncountable-v-singular-sets
kind: claim
title: Under every identification of its Bernoulli space with Cantor space, a group that is not virtually cyclic acts by homeomorphisms with uncountably many V-singular points
distinct_from:
  infinite-support-coordinate-permutations-are-nowhere-v-germs: that covers only identifications by relabeling coordinates, and there every point is singular, for every infinite group; this covers every homeomorphic identification, and gives uncountably many singular points when the cyclic subgroup has infinite index.
  shell-cantor-embeddings-are-finite-germ-extensions: that gives every countable group a shell action with finitely many V-singular points per element; this shows that no conjugate of a Bernoulli action of a group that is not virtually cyclic can play that role.
artifacts:
  - research/artifacts/shell-envelope-local-tests-2026-09-13.md
---

**ESTABLISHED.** Let `C = {0,1}^N` carry the standard binary Thompson group `V`.
For a homeomorphism `f` of `C`, call `x` a **V-singular point** of `f` if no
element of `V` agrees with `f` on any neighbourhood of `x`.

Let `Gamma` be a countable group with Bernoulli action on `X = {0,1}^Gamma`,
`(beta_g x)(k) = x(g^(-1) k)`. Let `h : X -> C` be any homeomorphism.

**Theorem.** If `g != 1` and `<g>` has infinite index in `Gamma`, then the set of
V-singular points of `h beta_g h^(-1)` is uncountable.

**Consequence.** If `Gamma` is not virtually cyclic, every nontrivial element of
`h beta(Gamma) h^(-1)` has uncountably many V-singular points. So no subgroup of
`Homeo(C)` containing `h beta(Gamma) h^(-1)` is a finite germ extension of `V`
in the sense of Belk–Hyde–Matucci (arXiv:2407.03149), whose definition requires
every element to have finitely many singular points.

**Scope.**
- The base group is `V`. A larger base containing `h beta(Gamma) h^(-1)` is not
  addressed.
- Free actions have empty fixed sets and are not covered. That includes free
  subshifts of `Gamma`.
- Nothing is asserted about finite presentation.
- The result is elementary and no novelty is claimed.
