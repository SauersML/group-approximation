---
rg: 2
id: full-shifts-with-different-alphabets-are-not-conjugate-proof
kind: route
title: An equivariant injection restricts to an injection between the constant configurations
target: full-shifts-with-different-alphabets-are-not-conjugate
requires: []
artifacts:
  - research/artifacts/gk-p-inf-wild-borel-and-topological-2026-09-12.md
---

Proposition 3.0 of the artifact.

1. With `(g.x)(h) = x(g^-1 h)`, a configuration `x` is fixed by every `g` exactly when
   `x(h) = x(1)` for all `h`. So `Fix_G(A^G)` is the set of `|A|` constant configurations.
2. Let `phi: A^G -> B^G` be equivariant and injective. For fixed `x`,
   `g.phi(x) = phi(g.x) = phi(x)`, so `phi` maps `Fix_G(A^G)` injectively into `Fix_G(B^G)` and
   `|A| <= |B|`.
3. A conjugacy and its inverse give `|A| = |B|`.

Neither continuity nor anything about `G` beyond equivariance is used. The same count works for
every finite-index subgroup `K`, with `|A|^[G:K]` points fixed by `K`.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 15 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
