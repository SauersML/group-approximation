---
rg: 2
id: sl4z-representations-have-sl2-invariant-vectors-citation
kind: route
title: Import Magee--de la Salle Theorem 1.1 and Corollary 1.3
target: sl4z-representations-have-sl2-invariant-vectors
requires: []
artifacts:
  - research/artifacts/mf-kazhdan-cstar-literature-status-2026-09-12.md
---

Source: M. Magee and M. de la Salle, *SL_4(Z) is not purely matricial field*,
arXiv:2312.03220v2 (30 Jan 2024), C. R. Math. 362 (2024) 903--910.  Read from
the arXiv PDF on 2026-09-12.

> **Theorem 1.1.** Every finite dimensional unitary representation of SL4(Z)
> contains a non-zero SL2(Z)-invariant vector.

with `SL_2(Z)` the upper-left block (p. 1), and

> **Corollary 1.3.** SL4(Z) is not purely matricial field.

whose proof (p. 2) gives `||rho(S+S^-1+T+T^-1)|| = 4` for every
finite-dimensional `rho` and `||lambda_SL4(Z)(S+S^-1+T+T^-1)|| =
||lambda_SL2(Z)(S+S^-1+T+T^-1)|| < 4`.  The proof of Theorem 1.1 reduces by
Bass--Milnor--Serre to Proposition 2.1 for `SL_4(Z/NZ)`.

Overgroups: for `Gamma >= SL_4(Z)` and a finite-dimensional `rho` of `Gamma`,
`rho|_(SL_4(Z))` is finite-dimensional, so `||rho(S+S^-1+T+T^-1)|| = 4`, and
`lambda_Gamma|_(SL_2(Z))` is a multiple of `lambda_(SL_2(Z))`.
