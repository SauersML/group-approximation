---
rg: 2
id: houghton-h3-polynomial-dehn-via-five-families
kind: route
title: Bound the five three-ray families polynomially and apply the three-ray path-word reduction
target: houghton-group-h3-has-polynomial-dehn-function
requires:
  - houghton-h3-dehn-polynomial-iff-five-three-ray-families
  - houghton-h3-five-three-ray-families-have-polynomial-area
artifacts:
  - research/artifacts/zp-houghton-three-rays-2026-09-18.md
---

By `houghton-h3-dehn-polynomial-iff-five-three-ray-families` (Theorem A of the
artifact), `δ_(H_3)(L) <= C L^6 (Φ(L+C) + L)`. If
`houghton-h3-five-three-ray-families-have-polynomial-area` gives `Φ(k) ≼ k^d`, then
`δ_(H_3)(x) ≼ x^(6 + max(d,1))`.

The only open input is the family bound. The families are

- one far commutation `F_3` on a ray;
- one reroute `R_3` of a deep transposition between the two other rays;
- three edge commutations `B_3`, `C_3`, `D_3` whose parts share a ray.

By Lemma C.1 of the artifact, the last three cannot be proved by moving to disjoint
ray supports.
