---
rg: 2
id: bernoulli-witness-read-degree-bound-proof
kind: route
title: Chain rule over the codewords reading one site bounds its information by their total entropy
target: bernoulli-witness-information-is-bounded-by-code-reads
requires: []
artifacts:
  - research/artifacts/rokhlin-window-localization-and-read-bound-2026-09-12.md
---

Theorem 2.1 of the artifact.

- `f e = 1` iff `f = e^-1`, so exactly `m = |F ∩ E^-1| <= |E|` codewords read the site `1`.
- The other codewords are functions of `x` on sites other than `1`, so they are independent of
  `x(1)`. The chain rule gives
  `I(x(1); y_F) = I(x(1); y_(F ∩ E^-1) | y_(F \ E^-1)) <= H(y_(F ∩ E^-1))`.
- Each `y_f` reads `|E|` distinct sites with iid values, so it has the law of `psi(x|_E)`, and
  subadditivity gives `H(y_(F ∩ E^-1)) <= m H(psi)`.
- `I(x(1); y_F) <= H(x(1)) = k log q`.
- Substituting into `Phi = (1/k)[H(psi) + k log q - I]`, together with `Phi >= H(psi)/k`, gives
  `Phi >= max{H(psi)/k, log q - (m-1)H(psi)/k} >= log q/m`.

Independently re-derived 2026-09-12 by w4-vf-positive-b: PASS (Section 7.2 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`).
- **Re-derived:** the chain rule step, the subadditivity step and the minimization over `H(psi)/k`.
- **Wording point:** the claim's Consequence uses `m`, bound to `|F ∩ E^-1|`, as if it were a free integer.
  As written, its hypothesis never holds.
