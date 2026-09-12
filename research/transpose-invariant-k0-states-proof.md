---
rg: 2
id: transpose-invariant-k0-states-proof
kind: route
title: Transpose-inverse fixes monomial units and reflections, twists the Hadamard unit by z, and commutes with the halving map
target: anti-central-k0-states-can-be-chosen-transpose-invariant
requires:
  - twisted-leavitt-k0-states-can-be-chosen-halving-invariant
artifacts:
  - research/artifacts/hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md
---

Section 3 of the artifact.
- **Proposition 3.1:**
  - Monomial units satisfy `g^* = g^(-1)` and reflections satisfy `tau_C^* = tau_C`, so `alpha` fixes `E x| V`.
  - On constants `alpha` is transpose-inverse, giving `alpha(h) = zh` and `alpha(hw) = -hw`.
- **Corollary 3.2:**
  - `alpha_*` fixes `e_-` and `[d]` and commutes with `delta_*`, so it commutes with the halving map `F_*`.
  - Markov–Kakutani for the two commuting affine maps `s -> s o alpha_*` and `s -> 2 s o F_*` gives a common fixed point.
  - Invariance under `alpha_*` gives `s(c_1) = s(c_2)`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 15 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *`alpha = (·*)^-1` fixes monomial units and reflections, and commutes with `delta`;*
- *`alpha(h) = zh`, so `alpha_*` sends `c_2` to `eps_- - c_2 = c_1`;*
- *both affine maps preserve states and commute, and Markov–Kakutani gives a common fixed point.*
