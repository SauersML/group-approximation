---
rg: 2
id: word-energy-subgroup-membership-proof
kind: route
title: Telescope subgroup words and complete finite coset paths
target: word-energy-domination-is-free-subgroup-membership
requires: []
artifacts:
  - notes/PROPERTY_T_FREE_CONTEXT_ENERGY_2026-09-07.md
---

For membership, write the target as `L` subgroup-generator factors.
Telescoping, unitary invariance and Cauchy--Schwarz give the constant
`L^2`, including inverse factors because
`||(V^{-1}-I)xi||=||(V-I)xi||`.

For nonmembership, use the left coset action of `F` on `F/H`, where
`H=<v_1,...,v_k>`. Retain only the suffix paths of the specified words
starting at `H`; there are at most `1+|w|+sum_j|v_j|` vertices. Every
partial generator translation extends to a permutation on this same finite
set by matching the domain and range complements. Inverse edges are also
preserved. The resulting matrices fix `delta_H` under each `v_j`, and
`w` moves it to an orthogonal basis vector. Evaluate the proposed operator
inequality there to get `2<=0`.

Sections 1 and 2 of the artifact supply the full proof and quantifiers.
