---
rg: 2
id: chain-transitive-core-has-no-transient-points-proof
kind: route
title: Follow the orbit into the omega-limit, chain across the core, and re-enter through the alpha-limit
target: chain-transitive-core-has-no-transient-points
requires: []
artifacts:
  - research/artifacts/un-hh-extension-toeplitz-subshift-2026-09-13.md
---

Let `x in X`, `eps > 0` and `delta = eps/2`. The limit sets `omega(x)` and `alpha(x)` are nonempty, closed and invariant,
and they lie in `CR(T)`.

- Pick `N` with `d(T^N x, q) < delta` for some `q in omega(x)`, and `M` with `d(T^{-M} x, r) < delta` for some
  `r in alpha(x)`.
- Chain transitivity gives a `delta`-chain `q = y_0, ..., y_k = r`.
- The sequence `x, Tx, ..., T^{N-1}x, y_0, ..., y_{k-1}, T^{-M}x, ..., T^{-1}x, x` is an `eps`-chain from `x` to itself.
- The first junction satisfies `d(T T^{N-1}x, y_0) < delta`. The second satisfies
  `d(T y_{k-1}, T^{-M}x) <= d(T y_{k-1}, r) + d(r, T^{-M}x) < eps`.
- Every other step is an exact orbit step.

So `x` is chain recurrent. A minimal set is chain transitive, because every orbit in it is dense.
