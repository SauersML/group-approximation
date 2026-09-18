---
rg: 2
id: houghton-five-ray-pours-by-shared-route-splitting
kind: route
title: Split the pour and commute the correction pour past each half of the middle pour, changing its route in between
target: houghton-five-ray-pour-route-change-is-polynomial
requires: []
artifacts:
  - research/artifacts/zp-houghton-five-rays-2026-09-17.md
  - experiments/houghton-five-rays-2026-09-17/verify_splitting.py
---

The complete proof is in `research/artifacts/zp-houghton-five-rays-2026-09-17.md`,
§§1–3.

1. Split `E^c_(a,b)(m)` as `λ_ad^(m_1) · X · Y · Z · λ_db^(m_1)`, where:
   - `X = E^a_(d,c)(m_1)`;
   - `Y = E^c_(a,b)(m_2)`;
   - `Z = E^b_(c,d)(m_1)`.

   This takes `2m_1` insertions.
2. Route `Y` via the one auxiliary ray `e`, so `Y = λ_ae^(m_2) λ_eb^(m_2)`.
3. Commute `X` past `Y` in two stages:
   - route `X` via `b`, then move it past `λ_ae^(m_2)` (ray supports `{b,c,d}` and
     `{a,e}`);
   - reroute it via `a`, then move it past `λ_eb^(m_2)` (ray supports `{a,c,d}` and
     `{b,e}`).

   Each half of `Y` commutes with `X` as a permutation, so the move is sound.
4. Route `Z` via `a`, cancel `XZ`, and route `Y` via `d`.

This gives `W(m_1+m_2) <= 3W(m_1) + 2W(m_2) + 4m_1m_2 + 4m_1`. Halving gives
`W(2^j) <= 5W(2^(j-1)) + 2·4^j`, so `W(m) <= 45 m^(log_2 5)`.

The script executes the nine-step derivation literally on words. It covers all
120 ray labelings and `1 <= m_1, m_2 <= 6`, checking each move and every
intermediate permutation.
