---
rg: 2
id: locally-finite-hnn-regular-rank-model-proof
kind: route
title: Regular representations of finite exhausting subgroups with permutation intertwiners for every conjugation, and the D_8 rank count
target: locally-finite-hnn-data-allow-independent-cylinder-defects
requires: []
artifacts:
  - research/artifacts/locally-finite-conjugation-defect-firewall-2026-09-12.md
---

Complete proof: artifact Sections 1–2.

- **Stages.** Exhaust `L` by finite subgroups `H_n`, and use the left regular representation of
  `H_n` on `F_2[H_n]`.
- **Intertwiners.** For each conjugator `u`, `K_(n,u) = H_n cap u^-1 H_n u` acts freely on `H_n`, and
  so does `u K_(n,u) u^-1`, with the same number of orbits. Match the orbits and apply `phi_u` inside
  each: that gives a permutation `pi_(n,u)` with `pi lambda(k) pi^-1 = lambda(u k u^-1)`.
- **Limit.** The ultraproduct satisfies every defining relation exactly, hence is a homomorphism on
  `Lambda`.
- **Ranks.** `F_2[H_n]` is free over `F_2[Q]` for finite `Q <= H_n`, which gives the free profile.
- **No fixed vectors.** A vector fixed by `sigma(L)` is almost fixed by each finite `H_m`, so its rank
  is at most `1/|H_m|`, which tends to `0`.
- **Defects.** Disjoint configurations span `D_8 x ... x D_8 <= L`, and ranks of tensor products
  multiply. In `F_2[D_8]`, `x + 1` has rank 4 and `(y+1)(x+1)` has rank 3, so the normalized ranks are
  `1/2`, `3/8` and `(3/8)^k`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 15.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
