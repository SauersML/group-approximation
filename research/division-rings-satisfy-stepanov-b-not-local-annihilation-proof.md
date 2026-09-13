---
rg: 2
id: division-rings-satisfy-stepanov-b-not-local-annihilation-proof
kind: route
title: Equation count for (b) over M_m(D), and matrix units killing local annihilation
target: division-rings-satisfy-stepanov-b-not-local-annihilation
requires: []
artifacts:
  - research/artifacts/un-stepanov-credit-2026-09-13.md
---

Complete elementary proof; see artifact §2.

**(b) for `R = M_m(D)`, `n ≥ 3`.** Identify `R^n` with `nm × m` matrices over `D`, and let `U ∈ GL_(nm)(D)` be the
block matrix of `u ∈ GL_n(R)`. Take `b = 1`. Restrict to columns `α` whose only nonzero `D`-column is the first, so
`α` is a vector `v ∈ D^(nm)`. The condition `α_i = 0` says the `i`-th block of `v`, `m` coordinates, vanishes. The
condition `(uα)_j = 0` says the `j`-th block of `Uv`, `m` more coordinates, vanishes. That is `2m` right-linear
equations in `nm ≥ 3m` unknowns over the division ring `D`, so a nonzero `v` exists, hence a nonzero `α`. The
counting is orientation-free: the same equation count works for rows, and for either conjugation convention `u^b`,
since `b = 1`.

**Local annihilation fails.** Let `F = {E_(ij) : 1 ≤ i, j ≤ m}`. Suppose `t ≠ 0` and `t E_(ij) s = 0` for all `i, j`.
The `(p, q)` entry of `t E_(ij) s` is `t_(pi) s_(jq)`. Pick `(p, i)` with `t_(pi) ≠ 0`, which is invertible in `D`;
then `s_(jq) = 0` for all `j, q`, so `s = 0`. Hence `S_F = {0}`, the non-unital ring it generates is `0`, and since
`R ≠ 0` this is not `R`. ∎
