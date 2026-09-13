---
rg: 2
id: v-rank-order-char-cycle-law-proof
kind: route
title: The order-characteristic cycle law is the cyclic case of trivial plus regular on finite subgroups of V
target: v-rank-order-char-cycles-are-trivial-plus-regular
requires:
  - v-rank-functions-are-trivial-plus-regular-on-cylinder-groups
artifacts:
  - research/artifacts/thompson-v-rank-functions-regular-on-cylinder-groups-2026-09-12.md
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
---

This is artifact Corollary 1.2 (w7-v-cycle-c2). `w3-vf-linear` re-derived it in Section 32 of its verification artifact.

**Proof.**
- Let `char F = p` and let `s` be a clopen `p`-cycle.
- Apply `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups` to the finite subgroup `G = <s>` and
  `A = (1 - [s])^j`.
- For `j >= 1`, `eps(A) = 0`.
- In `F[Z/p] = F[y]/(y^p)` with `y = 1 - [s]`, left multiplication by `y^j` has rank `p - j`.
- So `rk((1 - [s])^j) = (1 - phi_V)(p - j)/p` for `1 <= j <= p`.

**Cross-check for `p = 2`** (artifact Section 2, no characters).
- **Setup.** Take a clopen `q`-cycle `c` with `t c t = c^(-1)`, and let `e = sum_i [c]^i`.
- **Lower bound.** The identity `1 - e = u(1 + [t]) + (1 + [t])[t]u[t]` gives `rk(1 + [t]) >= (1 - phi_V)(q - 1)/(2q)`.
- **Upper bound.** A square-zero corner bound gives `rk(1 + [t]) <= (1 - phi_V)(q + 1)/(2q)`.
- **Conclusion.** Letting `q -> infinity` gives `rk(1 + [t]) = (1 - phi_V)/2`.
