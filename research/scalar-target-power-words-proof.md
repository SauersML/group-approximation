---
rg: 2
id: scalar-target-power-words-proof
kind: route
title: Companion matrix gives an exact e-th root of any scalar
target: scalar-target-power-words-have-exact-roots
requires: []
artifacts:
  - research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md
---

Proof of `scalar-target-power-words-have-exact-roots` (artifact Section 2).

Let `C in M_e(K)` be the companion matrix of `x^e - lambda`: `C e_i = e_(i+1)` for `1 <= i < e` and
`C e_e = lambda e_1`. Then for each `i`, `C^e e_i = lambda e_i`, so `C^e = lambda 1_e`. Its determinant
is `(-1)^(e-1) lambda != 0`, so `C in GL_e(K)`. Tensoring, `(C (x) 1_d)^e = lambda 1_(ed)`. Valid in
every characteristic, with no Jordan or `p`-divisibility hypothesis, because the target is central.

This is the `l = 1` instance of `rgr-p-cyclic-twist-system-proof`: one block-equation `P_0 = lambda`,
solved by the single twist `b_0 = C`.
