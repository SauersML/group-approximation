---
rg: 2
id: sl3z-pmf-iff-affine-kazhdan-group-pmf-proof
kind: route
title: Permanence for the amenable kernel Z^3 in one direction, restriction of the regular representation in the other
target: sl3z-pmf-iff-affine-kazhdan-group-pmf
requires: [pmf-permanence-amenable-kernel-without-exactness]
artifacts:
  - research/artifacts/sl3z-pmf-affine-reformulation-2026-09-13.md
---

Artifact, Section 3.

- `=>`: `pmf-permanence-amenable-kernel-without-exactness` with `A = Z^3`,
  `A_N = N! Z^3` and `Q = SL_3(Z)`.
- `<=`: `l^2(P)` is the orthogonal sum over right cosets `SL_3(Z) g` of
  `SL_3(Z)`-invariant subspaces, each unitarily equivalent to
  `lambda_(SL_3(Z))`.  So `||lambda_P(z)|| = ||lambda_(SL_3(Z))(z)||` for `z` in
  `C[SL_3(Z)]`, and restricting a strongly convergent sequence for `P` gives
  one for `SL_3(Z)`.
- MF: the permanence proof works with asymptotic homomorphisms in place of
  representations.  Also, `C*_r(SL_3(Z)) <= C*_r(P)`, and MF passes to
  C*-subalgebras.
- Property (T) of `Z^n x| SL_n(Z)` for `n >= 3` is classical (import).
