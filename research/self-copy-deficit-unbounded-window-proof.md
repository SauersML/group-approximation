---
rg: 2
id: self-copy-deficit-unbounded-window-proof
kind: route
title: Seward's formula turns one deficit into zero supremum, the finitary infimum into collapse, and the read bound into large windows
target: self-copy-host-rokhlin-deficits-need-unbounded-windows
requires:
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - rokhlin-supremum-dichotomy-with-centralized-self-copies
  - bernoulli-witness-information-is-bounded-by-code-reads
artifacts:
  - research/artifacts/rokhlin-window-localization-and-read-bound-2026-09-12.md
---

Theorem 3.1 of the artifact.

1. A configuration with `Phi < log q` gives `rho_q(G) = inf Phi < log q`, so some `k` has
   `h^Rok_G((A^k)^G) < k log q`.
2. By item 1 of Seward's import that value is `min{k log q, h_sup(G)}`, so `h_sup(G)` is finite,
   hence `0` by hypothesis. The dichotomy claim supplies the hypothesis for groups containing their
   own square and finite subgroups of unbounded order.
3. Then `h^Rok_G(L^G) = min{H(L), 0} = 0` for every finite base, so `rho_(q')(G) = 0` for every
   `q'`, and by the finitary-witness claim configurations of arbitrarily small value exist at every
   alphabet.
4. The read-degree bound gives `Phi >= log q'/|F ∩ E^-1|` and `Phi >= H(psi)/k`, so a configuration
   with `Phi < log q'/m` has `|E| >= |F ∩ E^-1| > m` and `H(psi)/k < log q'/m`.

Independently re-derived 2026-09-12 by w4-vf-positive-b: PASS (Section 7.3 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`).
- **Re-derived:** steps 1–4, against Seward's item 1, the finitary infimum and the dichotomy
  corollary as stated on main.
- **Note:** here `m` in step 4 is a free integer, which is how the read-bound claim's Consequence
  should also be stated.
