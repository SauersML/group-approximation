---
rg: 2
id: almost-commuting-opposite-higman-generators-force-collapse
kind: claim
title: If two opposite Higman generators almost commute in a bi-invariant metric, every generator is almost trivial
distinct_from:
  one-small-higman-generator-collapses-the-four-cycle: that collapses the cycle in operator norm once one generator lies in a small spectral basin; this collapses it in any bi-invariant metric once two opposite generators almost commute, with no spectral assumption.
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

**ESTABLISHED** by `almost-commuting-higman-collapse-proof` (elementary; no
novelty claimed).

**Statement.** Let `Gamma` be a group with a bi-invariant metric `rho`, and write
`l(x) = rho(x, 1)`. Let `a, b, c, e` be in `Gamma` with

```text
rho(a^-1 b a, b^2), rho(b^-1 c b, c^2), rho(c^-1 e c, e^2), rho(e^-1 a e, a^2) <= delta,
rho(ac, ca) <= eta.
```

Then `max(l(a), l(b), l(c), l(e)) <= 63 delta + 24 eta`. By the cyclic symmetry of
the relations, the same bound holds when `b` and `e` almost commute instead.

**Scope.** Bi-invariant metrics include:
- normalized Hamming distance on `Sym(n)`, the soficity metric;
- normalized Hilbert--Schmidt distance on `U(n)`;
- operator-norm distance on `U(n)`;
- the discrete metric.

With `delta = eta = 0` and the discrete metric this recovers the exact corollary
of `nontrivial-higman-quotients-keep-all-four-bs-subgroups`: a quotient of Higman's
group in which `a` and `c` commute is trivial.

**Reading for sofic approximations.** Take a sequence of approximate
permutation representations of a nontrivial quotient of `H4` in which some
generator stays macroscopically far from `1`. The commutator `[a, c]` must also
stay macroscopically far from `1`, with explicit constants.
