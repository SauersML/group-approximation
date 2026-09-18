---
rg: 2
id: houghton-h3-five-families-reduce-to-reroute
kind: route
title: Conjugate each three-ray family by a pull so that one part becomes a single τ, reroute the other part off its ray, and pay only reroutes R_3
target: houghton-h3-five-three-ray-families-have-polynomial-area
requires:
  - houghton-h3-reroute-family-has-polynomial-area
artifacts:
  - research/artifacts/zp-houghton-h3-families-via-reroute-2026-09-18.md
  - research/artifacts/zp-houghton-three-rays-2026-09-18.md
  - experiments/houghton-h3-families-2026-09-17/verify_h3_families.py
  - experiments/houghton-h3-families-2026-09-17/verify_h3_families.out
---

The complete proof is Lemmas 2–5 and §6 of
`research/artifacts/zp-houghton-h3-families-via-reroute-2026-09-18.md`. Here
`R̄(k) = max_(m <= k) R_3(m)`, and `F'(k)` is the area of `τ_x D τ_x D`.

- **F_3 (Lemma 2).** Conjugate by `λ_ux^2`. The relator `λ_ux^2 τ_x λ_xu^2 = τ_u` of
  `Q` turns the relation into `[τ_u, D^u_x(k-2)]`. Reroute to the third ray and
  commute. This gives `F_3(k) <= 2R_3(k-2) + 6k + 2`.
- **D_3 (Lemma 3).** Split `λ_wz = λ_wx λ_xz` and `λ_zw = λ_zx λ_xw`. Pushing is then
  literal, pulling takes two Q-steps, and in between is one reroute at each of the two
  scales. This gives `D_3(j) <= R_3(j) + R_3(j-1) + 4`.
- **B_3 (Lemma 4).**
  - Reroute `Ed t_x(i)` to route `y` and `Ed t_y(j)` to route `x`.
  - Conjugate by `λ_xy^(j-1)`. The relation becomes literally
    `D^y_x(i+j-2) τ_y D^y_x(i+j-2) τ_y`, plus a cancelling tail.
  - Reroute to the third ray and commute.

  This costs `6 R̄(i+j) + O(i+j)`.
- **C_3 (Lemma 5).** Conjugate by `λ_pq`, which sends `Ed σ_{p,q}` to `τ_p`.
  - If the ray edge is on the third ray, use `D_3` and one reroute.
  - If it is on the `τ`-ray, one reroute and the relation is literally an `F'` word.
  - If it is on the other endpoint, one reroute, two pulls, one reroute, then commute.

**Where Lemma C.1 does not apply.** Lemma C.1 of
`research/artifacts/zp-houghton-three-rays-2026-09-18.md` rules out rerouting *the
given parts* to disjoint ray supports. Conjugating the whole relation changes the
parts: one of them becomes a single letter `τ`, whose ray support has size one.

**Total.** `Φ(k) <= 6 R̄(2k) + 14k + 11`, which is polynomial by the required claim.
The script checks all 4986 derivations literally, for every labeling and route
function and for small indices.
