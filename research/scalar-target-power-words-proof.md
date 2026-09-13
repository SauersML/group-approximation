---
rg: 2
id: scalar-target-power-words-proof
kind: route
title: Companion matrix gives an exact e-th root of any scalar
target: scalar-target-power-words-have-exact-roots
requires:
  - rgr-p-reduces-to-cyclic-twist-system
artifacts:
  - research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md
---

Proof of `scalar-target-power-words-have-exact-roots` (artifact Section 2).

For `e > 0`, let `C in M_e(K)` be the companion matrix of `x^e - lambda`: `C e_i = e_(i+1)` for `1 <= i < e`
and `C e_e = lambda e_1`. Then for each `i`, `C^e e_i = lambda e_i`, so `C^e = lambda 1_e`. Its determinant
is `(-1)^(e-1) lambda != 0`, so `C in GL_e(K)`. Tensoring, `(C (x) 1_d)^e = lambda 1_(ed)`. Valid in
every characteristic, with no Jordan or `p`-divisibility hypothesis, because the target is central.

For `e < 0`, `t^e = lambda 1` iff `(t^(-1))^|e| = lambda 1`, so `t = C^(-1)`, with `C` the companion matrix
of `x^|e| - lambda`, is a solution. Alternatively `t = C'`, with `C'` the companion matrix of
`x^|e| - lambda^(-1)`: then `t^e = (C'^|e|)^(-1) = lambda 1`.

This is the `l = 1` instance of `rgr-p-cyclic-twist-system-proof`: `C (x) 1_d` is the twisted cyclic shift on
`|e|` blocks with twists `1, ..., 1, lambda 1_d` (for `e < 0`, `C' (x) 1_d`, with last twist
`lambda^(-1) 1_d`), and every rotation `P_m` equals `lambda 1_d`. (Corrected by w5-rgr-p: an earlier line
described this as one block-equation `P_0 = lambda` solved by the single twist `b_0 = C`.)

*Verification by `w4-vf-linear-b` (2026-09-12), Section 30.2 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Checked: `C^e e_i = lambda e_i`, and `det C = (-1)^(e-1) lambda`. Precision: for `e < 0`, use the companion matrix of `x^|e| - lambda^(-1)` and invert.*
