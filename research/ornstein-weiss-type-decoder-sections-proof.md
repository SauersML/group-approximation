---
rg: 2
id: ornstein-weiss-type-decoder-sections-proof
kind: route
title: The coboundary equation along one element yields a nonconstant invariant function of an ergodic skew product
target: ornstein-weiss-type-decoders-admit-no-measurable-section
requires: []
artifacts:
  - research/artifacts/ornstein-weiss-decoder-sections-2026-09-12.md
---

Direct proof, Sections 1–2 of `research/artifacts/ornstein-weiss-decoder-sections-2026-09-12.md`.

1. **Reduction.** Equivariance reduces a section to a Borel `p` with `p(x) - p(a^-1.x) = lambda(x(1))`.
2. **Finite order `N`.** Summing over `k < N` gives `sum lambda(x(a^k)) = 0` almost everywhere, but that sum is
   uniform on `Z/n`.
3. **Infinite order.** `F(x, eps) = omega^(eps + p(x))` is invariant under
   `S_f(x, eps) = (a^-1.x, eps + lambda(x(1)))` and is not constant.
   - `S_f` splits over the right cosets of `<a>`.
   - On `<a>` itself, partial sums `s_(k+1) = s_k + lambda(x(a^k))` conjugate `S_f` to a Bernoulli shift.
   - The other cosets form a Bernoulli shift.
   - A product of mixing transformations is ergodic, a contradiction.
