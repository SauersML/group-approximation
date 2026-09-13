---
rg: 2
id: pure-braid-sunflower-characters-obstruct-bnsr-invariants
kind: claim
title: "Characters on a sunflower of puncture sets U_1..U_r (pairwise meeting in one puncture) miss Sigma^D(P_n), D = sum(|U_i| - 3)"
distinct_from:
  pure-braid-product-projections-obstruct-bnsr-invariants: that claim uses disjoint strand blocks in P_n; this is its S_{n+1}-symmetric form on the n+1 punctures of the sphere, which also covers blocks through the point at infinity.
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-pencils-2026-09-13.md
---

Identify characters of `H_n = P_n / Z(P_n) = PMod(S_{0,n+1})` with symmetric
arrays `c_{st}` (`s != t` in `{1, ..., n+1}`) with all row sums zero, where
`c_{st}` is the value on a Dehn twist about a curve around punctures `s, t`.
For `U <= [n+1]`, let `L_U` be the characters supported on pairs inside `U`.

If `U_1, ..., U_r` have `|U_i| >= 4` and pairwise intersect in one common
puncture `p`, then every nonzero character in `L_{U_1} + ... + L_{U_r}` lies
outside `Sigma^D(H_n)`, and its pullback lies outside `Sigma^D(P_n)`, where
`D = sum_i (|U_i| - 3)`.

For `n = 5` and `D = 2` this gives the six 5-dimensional subspaces `L_U`
(`|U| = 5`) outside `Sigma^2(P_5)`. The sixth, `U = {1,...,5}`, is the set of
characters whose rows `sum_{j != i} a_{ij}` all vanish.

Status: UNREVIEWED (lane z1-09-pure-braid, 2026-09-13).
