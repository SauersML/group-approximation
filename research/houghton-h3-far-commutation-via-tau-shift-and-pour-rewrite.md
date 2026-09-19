---
rg: 2
id: houghton-h3-far-commutation-via-tau-shift-and-pour-rewrite
kind: route
title: Shift the far transposition to the top of ray b with the τ relator, reroute it through ray c, and read the reroute as a commutation of τ_b with one pour
target: houghton-h3-far-commutation-bounded-by-two-ray-pour-rewrite
requires:
  - houghton-dehn-polynomially-equivalent-to-commutation-area
  - houghton-four-ray-pour-route-change-bounded-by-h3-dehn
artifacts:
  - research/artifacts/zp-houghton-h3-far-commutation-via-pour-rewrite-2026-09-18.md
  - experiments/houghton-h3-2026-09-17/verify_far_commutation_via_pour_rewrite.py
---

The complete proof is Steps 1–4 of
`research/artifacts/zp-houghton-h3-far-commutation-via-pour-rewrite-2026-09-18.md`.

Imports:

- the presentation recipe (Lee Theorem C and Lemma 3 of part 1), from
  `houghton-dehn-polynomially-equivalent-to-commutation-area`;
- the element identity `E^z_(x,y)(m) = λ_xy^m ρ_y(m)` (Lemma 1), from
  `houghton-four-ray-pour-route-change-bounded-by-h3-dehn`. Its proof is valid for any
  `n >= 3`, and the script re-checks it for `H_3`.

Steps:

1. Conjugate `w_k` by `λ_ab^k` and use the `Q`-relator
   `τ_a = λ_ab^2 τ_b λ_ba^2`. This gives `[D^a_b(k-2), τ_a]` at cost `4k+2`.
2. Reroute `D^a_b(k-2)` to `D^c_b(k-2)`, whose letters commute with `τ_a`. This gives
   `Area(w_k) <= 2R(k-2) + 6k`.
3. The reroute word is cyclically `τ_b V τ_b V^(-1)` with `V = E^b_(a,c)(j)`, as in
   Lemma 2.1 of the six-ray note. No auxiliary ray is needed.
4. Replace `V` by the two-ray word `N_(a,c)(j)`, whose letters avoid ray `b`. This
   gives `R(j) <= 2A_3(j) + j^3 + 4j + 2`.
