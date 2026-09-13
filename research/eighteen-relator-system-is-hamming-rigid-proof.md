---
rg: 2
id: eighteen-relator-system-is-hamming-rigid-proof
kind: route
title: Ultraproduct of almost-solutions and simplicity of the presented group
target: eighteen-relator-system-is-hamming-rigid
requires: [thompson-steinberg-presentation-of-leavitt-unit-group, openai-leavitt-unit-nonsofic, binary-leavitt-unit-group-is-simple]
artifacts:
  - research/artifacts/thompson-steinberg-presentation-2026-09-12.md
---

Suppose the claim fails for some `epsilon > 0`. Then there are degrees `n_k` and permutations
`s^(k)_g in Sym(n_k)` whose relator defects are at most `1/k`, while
`max_g d_H(s^(k)_g, id) > epsilon`. Passing to a subsequence, one fixed generator `g_0` has
`d_H(s^(k)_(g_0), id) > epsilon` for all `k`.

Fix a nonprincipal ultrafilter `omega`. Let `G_omega = prod_omega Sym(n_k) / N_omega`, where
`N_omega` consists of the sequences with `d_H -> 0` along `omega`. The assignment
`g -> [s^(k)_g]` kills every relator, since the defects tend to `0`. So it defines a homomorphism
`pi : Q -> G_omega`, where `Q` is the presented group. The image of `g_0` is nontrivial.

`Q` is isomorphic to `L_(F_2)(1,2)^x` (`thompson-steinberg-presentation-of-leavitt-unit-group`),
which is simple (`binary-leavitt-unit-group-is-simple`). So `pi` is injective. A countable
group embedding in a metric ultraproduct of finite symmetric groups with normalized Hamming
distance is sofic (Elek--Szabó's characterization, the standard definition used throughout the
graph). So `L_(F_2)(1,2)^x` would be sofic, contradicting `openai-leavitt-unit-nonsofic`. QED.

The same argument with exact solutions shows the other half. Any exact solution in a sofic group
generates a quotient of `Q` inside a sofic group. That quotient is trivial, because a nontrivial
quotient of a simple group is the group itself, and a subgroup of a sofic group is sofic.
