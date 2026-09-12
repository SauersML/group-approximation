---
rg: 2
id: triangular-conjugate-bs-chains-proof
kind: route
title: Adjoin earlier generators by cyclic amalgams and pass to the limit
target: triangular-conjugate-bs-chains-are-sofic
requires: []
artifacts:
  - research/artifacts/triangular-bs-chain-proof-2026-09-07.md
---

Fix finitely many relation indices `D`. Start with the free group on the
generators outside `D`, and process the indices of `D` in decreasing order.
At step `i`, all letters of `c_i` already exist, and `c_i` has infinite
order: it is conjugate to a nonzero power of an existing infinite-order
generator. Attach `BS(l_i,k_i)=<z,t | t^(-1)z^(l_i)t=z^(k_i)>` by identifying
`t` with `c_i` along an infinite cyclic subgroup. Both factors embed by the
amalgam normal-form theorem, so all previous generators and the new `z=x_i`
retain infinite order. The factors are sofic and the edge is amenable, hence
the enlarged group is sofic. Tietze elimination of `t` gives exactly the
required next presentation, with no additional relations.

Thus every finite-relator truncation on the full generator set is sofic.
The full presentation is their directed colimit. The artifact proves
direct-limit permanence directly from the finite-table definition of
soficity; injectivity of the maps between truncations is not assumed.

The standard inputs and their precise roles, including the soficity and
infinite-order generators of `BS(l_i,k_i)`, are spelled out in the artifact.
