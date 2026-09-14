---
rg: 2
id: nonnegative-deficiency-kervaire-via-finite-whitehead
kind: route
title: Whitehead's asphericity conjecture forbids balanced Kervaire failures, and positive deficiency forbids the rest
target: kervaire-killing-form-holds-over-nonnegative-deficiency-groups
requires:
  - whitehead-asphericity-conjecture
  - deficiency-zero-kervaire-failure-yields-whitehead-counterexample
artifacts:
  - research/artifacts/ideas-bridges-2026-09-13.md
---

Let `G != 1` have a finite presentation with `m <= n`, and let
`w in G * <t>`.

- **If `m < n`:** item 1 of
  `deficiency-zero-kervaire-failure-yields-whitehead-counterexample` gives
  `G_w` infinite.
- **If `m = n` and `G_w = 1`:** item 2(c) of the same theorem gives a finite
  connected subcomplex `K` of a contractible 2-complex with `pi_2(K) != 0`.
  A contractible complex is aspherical, so this contradicts
  `whitehead-asphericity-conjecture`.

So `G_w != 1` in both cases.
