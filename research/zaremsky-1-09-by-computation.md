---
rg: 2
id: zaremsky-1-09-by-computation
kind: route
title: "Zaremsky 1.9 answered by computing Sigma^m(P_n) in the three ranges m = 1, 2 <= m <= n-3, m >= n-2"
target: zaremsky-1-09-bnsr-invariants-of-pure-braid-groups
requires:
  - pure-braid-bns-invariant-is-circle-complement
  - pure-braid-middle-bnsr-invariants-computed
  - pure-braid-top-bnsr-invariants-are-center-nonvanishing
---

The ranges cover every pair `(n, m)`:

- `m = 1`, all `n`: `pure-braid-bns-invariant-is-circle-complement`
  (Koban–McCammond–Meier);
- `m >= n - 2`, all `n >= 3` (and trivially `n <= 2`):
  `pure-braid-top-bnsr-invariants-are-center-nonvanishing`;
- `2 <= m <= n - 3`, which occurs only for `n >= 5`:
  `pure-braid-middle-bnsr-invariants-computed`.

For `n <= 4` the first two parts already give every invariant. This route is
the only admissible way to establish the root.
