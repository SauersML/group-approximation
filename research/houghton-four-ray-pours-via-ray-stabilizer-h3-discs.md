---
rg: 2
id: houghton-four-ray-pours-via-ray-stabilizer-h3-discs
kind: route
title: Split the four-ray skew square along a two-ray normal form into two discs in ray-stabilizer copies of H_3
target: houghton-four-ray-pour-route-change-bounded-by-h3-dehn
requires:
  - houghton-groups-have-at-most-exponential-dehn-function
artifacts:
  - research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md
  - experiments/houghton-four-rays-2026-09-17/verify_two_ray_factorization.py
---

The complete proof is §§1–3 (Lemma 1, Lemma 2, Theorem 3) of
`research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md`.

- **Lemma 1 (two-ray normal form).** `E^c_(a,b)(m) = λ_ab^m ρ_b(m)` as elements, where
  `ρ_b(m) = Π_(i=m-1..1) (s_1 ⋯ s_i)` and `s_j = λ_ba^(j-1) τ_b λ_ab^(j-1)` is the
  transposition `((b,j),(b,j+1))`. The first `m` letters shift ray `a` into ray `b`,
  and then `ρ_b(m)` reverses the order of the top `m` points of `b`. The word has length
  `m + Σ_(i<m) i^2 <= m^3`. The script checks the identity for all 24 labelings and
  `m <= 7`.
- **Lemma 2 (area transfer).** `S_x` is the pointwise stabilizer of ray `x`, and
  `S_x ≅ H_3`. The only import used is that `H_3` is finitely presented, via Lee's
  presentation, quoted verbatim in
  `houghton-groups-have-at-most-exponential-dehn-function`. With that, a
  null-homotopic `P`-word with letters in `S_x` has area
  `<= K(|w| + δ_(H_3)(C|w|))`. This is the standard translation of van Kampen diagrams
  through a pair of word maps.
- **Theorem 3.** `E^c (E^d)^(-1)` is freely equal to `(E^c N^(-1)) (N (E^d)^(-1))`.
  The first factor uses no letter touching ray `d`, and the second none touching ray
  `c`. Each factor has length `<= 2m^3`. Apply Lemma 2 with `x = d` and `x = c`.
