---
rg: 2
id: non-rf-hyperbolic-group-via-local-restricted-burnside
kind: route
title: A local restricted Burnside principle at a large odd exponent makes every large Delzant--Gromov stage non-residually-finite
target: non-residually-finite-hyperbolic-group
requires:
  - large-odd-exponent-local-restricted-burnside
  - local-restricted-burnside-iff-partial-burnside-finite-quotients
---

Take `m` and odd `N >= n_1(F_m)` given by `large-odd-exponent-local-restricted-burnside`,
so `LRB(m,N)` holds. By clause 5 of
`local-restricted-burnside-iff-partial-burnside-finite-quotients`, the stages
`G_k` of `free-burnside-is-a-limit-of-hyperbolic-groups` are not residually
finite for all sufficiently large `k`. Each `G_k` is word-hyperbolic (item 1 of
that import). So a word-hyperbolic group that is not residually finite exists. ∎
