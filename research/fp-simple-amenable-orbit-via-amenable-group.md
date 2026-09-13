---
rg: 2
id: fp-simple-amenable-orbit-via-amenable-group
kind: route
title: A finitely presented infinite simple amenable group realizes itself through its Bernoulli shift
target: fp-simple-group-in-amenable-orbit-full-group
requires:
  - fp-infinite-simple-amenable-group
---

Let `S` be a finitely presented infinite simple amenable group
(`fp-infinite-simple-amenable-group`). Take `Lambda = S` acting on
`X = {0,1}^S` by shifts, with the uniform product measure `mu`.

- **Essentially free.** For `g != 1`, `Fix(g)` is the set of configurations
  constant on every right coset of `<g>`. There are infinitely many cosets, each
  of size at least `2`, so `mu(Fix g) = 0`.
- **The realization.** `rho(g)` is the shift by `g`, with constant cocycle
  `c_g = g`, which has finite range. It is nontrivial on a set of measure one.

So `S` witnesses `fp-simple-group-in-amenable-orbit-full-group`. This records
that the amenable root implies the realization claim, which in turn implies the
hyperlinear root: amenable, then amenable-orbit realization, then sofic.
