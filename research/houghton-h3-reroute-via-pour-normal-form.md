---
rg: 2
id: houghton-h3-reroute-via-pour-normal-form
kind: route
title: Read the middle of D^u_x(k) D^v_x(k)^(-1) as one pour from u to v, replace it by its two-ray normal form, and commute τ_x across
target: houghton-h3-reroute-family-has-polynomial-area
requires:
  - houghton-three-ray-pours-have-polynomial-two-ray-normal-forms
artifacts:
  - research/artifacts/zp-houghton-h3-families-via-reroute-2026-09-18.md
  - research/artifacts/zp-houghton-pour-doubling-2026-09-18.md
  - experiments/houghton-h3-families-2026-09-17/verify_h3_families.py
  - experiments/houghton-h3-families-2026-09-17/verify_h3_families.out
---

The complete proof is Lemma 1 of
`research/artifacts/zp-houghton-h3-families-via-reroute-2026-09-18.md`.

1. **Convert.** After `2k + 1` letter conversions,
   `D^u_x(k) D^v_x(k)^(-1)` becomes `λ_xu^k τ_x · (λ_ux^k λ_xv^k) · τ_x λ_vx^k`.
2. **Replace.** Proposition 5 of the doubling note, for the labeling `(u,v,x)`,
   replaces the middle pour by the two-ray word `N_k` in `λ_uv, λ_vu, τ_u, τ_v`. That
   costs `A(k)`. The proposition is valid for every labeling, as Theorem 6 there uses
   it.
3. **Commute.** `τ_x` crosses `N_k` in `|N_k| <= k^5` relators of length 4, and
   `τ_x^2` cancels.
4. **Restore.** Put the pour back, at cost `A(k)`, and cancel `2k` inverse pairs.

This sidesteps the triangle relator `X_k^2` at which §5 of the doubling note stopped.
The script runs this derivation literally for all six labelings and `k <= 12`, and
checks every Q-step identity and the step count.
