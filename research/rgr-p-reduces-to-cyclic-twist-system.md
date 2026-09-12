---
rg: 2
id: rgr-p-reduces-to-cyclic-twist-system
kind: claim
title: RGR_p at amplification by the total exponent is exactly a cyclic scalar system in e matrix unknowns
requires:
  - rank-ultraproduct-unit-groups-solve-nonsingular-equations
artifacts:
  - research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `rgr-p-cyclic-twist-system-proof`; verification requested from
`w4-vf-linear-b`.

Fix `Fbar` algebraically closed of characteristic `p`, a word `w(t) = c_0 t^(e_1) c_1 ... t^(e_l) c_l`
with `c_i in GL_d(Fbar)` and `e = e_1 + ... + e_l != 0`.

**Statement.** Amplify by `k = e`. On `W = W_0 (+) ... (+) W_(e-1)` (`W_j = Fbar^d`) let `t` be the
twisted cyclic shift `t|_(W_j) = b_j : W_j -> W_(j+1 mod e)`, `b_j in GL_d`. Then `w(t)` is
block-diagonal and `rank(w(t) - lambda 1_(de)) = sum_(m=0)^(e-1) rank(P_m - lambda 1_d)`, where

```text
P_m = c_0 . B_1(m) . c_1 . ... . B_l(m) . c_l,
```

`B_i(m)` the ordered product of the twists met by the `i`-th syllable started at block `m`. So RGR_p at
this amplification is exactly: choose `b_0, ..., b_(e-1) in GL_d` and `lambda` making the `e` cyclic
products `P_m` simultaneously scalar, up to total rank `eps de`. For a positive word each `B_i(m)` is a
free element of `GL_d`, coupled across the `P_m` only by the cyclic reuse of the `b_j`.

This loses nothing: solving the cyclic system solves RGR_p for that word, and any RGR_p witness at
amplification `e` has this block form. The reduction holds for every `e != 0` (negative exponents give
inverse shifts).

## Attempts

- The `e` rotations are **not** mutually conjugate, because the fixed `c_i` do not rotate with the
  starting block; the coefficient-free conjugacy collapse does not apply.
- Rank slack over the `e` blocks lets one drop a fixed number of blocks, not an `eps`-fraction growing
  with amplification, because block-diagonality pins the cycle length to `e`.
