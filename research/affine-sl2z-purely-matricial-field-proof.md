---
rg: 2
id: affine-sl2z-purely-matricial-field-proof
kind: route
title: SL_2(Z) is PFF by induction from a free subgroup of index 12; apply amenable-kernel permanence with A = Z^2
target: affine-sl2z-purely-matricial-field
requires: [pmf-permanence-amenable-kernel-without-exactness]
artifacts:
  - research/artifacts/sl3z-pmf-affine-reformulation-2026-09-13.md
---

Artifact, Section 2.

1. Free groups are PMF (Magee--de la Salle p. 2, citing Haagerup--Thorbjørnsen)
   and PFF (Bordenave--Collins; import, not re-read).  The Sanov subgroup
   `<[[1,2],[0,1]], [[1,0],[2,1]]>` is free of index 12 in `SL_2(Z)`, since
   `Gamma(2) = {+-I} x F` has index 6.  Induction from a finite-index subgroup
   writes `Ind sigma(g)` as a `12 x 12` matrix over `sigma(C[F])` and sends
   `lambda_F` to `lambda_(SL_2(Z))`.  Matrix-coefficient strong convergence then
   gives strong convergence of the induced representations.
2. `pmf-permanence-amenable-kernel-without-exactness` with `A = Z^2`,
   `A_N = N! Z^2` and `Q = SL_2(Z)` makes `Z^2 x| SL_2(Z)` PFF.  The parabolic
   `Z^2 x| GL_2(Z)` is handled the same way, since `GL_2(Z)` contains `SL_2(Z)`
   with index 2.
3. Independently, Gao--Kunnawalkam Elayavalli--Mj, arXiv:2607.29571v1,
   Theorem 1.1 applies directly: `SL_2(Z)` is exact.
4. Relative property (T) for `(Z^2 x| SL_2(Z), Z^2)` is classical (Kazhdan;
   Burger; import), and it rules out the Haagerup property.
