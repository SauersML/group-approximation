---
rg: 2
id: stable-branch-trivializes-hs-block-programme-proof
kind: route
title: Collapse every almost-representation of the simple nonhyperlinear ambient group and use rank-one atoms
target: stable-branch-trivializes-hs-block-programme
requires: [steinberg-hs-stability-equals-nonhyperlinearity, leavitt-gl-equals-el-and-perfect-unit-group, binary-leavitt-elementary-group-is-simple, pointwise-hs-stability-from-no-hyperlinear-quotient, openai-nine-leaf-leavitt-configuration]
---

**Item 1.**  Assume the stable branch.

* By `steinberg-hs-stability-equals-nonhyperlinearity`, `Q = EL_4(R)` is
  nonhyperlinear.
* The prefix-code self-similarity `M_9(R) ~= R ~= M_4(R)`, together with
  `GL_n(R) = EL_n(R)` (`leavitt-gl-equals-el-and-perfect-unit-group`),
  identifies `G = EL_D(R) ~= EL_9(R)` with `Q`.  So `G` is nonhyperlinear.
* `G` is simple (`binary-leavitt-elementary-group-is-simple`), so its only
  quotients are `1` and `G`, and it has no nontrivial hyperlinear quotient.
* By `pointwise-hs-stability-from-no-hyperlinear-quotient`, every sequence of
  maps `phi_k : G -> U(d_k)` with pointwise vanishing defect converges
  pointwise to `1`.

If `eta(delta)` did not tend to `0`, there would be `eta_0 > 0`,
`delta_k -> 0`, `delta_k`-almost representations `phi_k`, and generators
`s_k` with `||phi_k(s_k) - 1||_2 >= eta_0`.  Finitely many generators occur,
so a subsequence fixes `s_k = s`.  The windows `ceil(1/delta_k)` exhaust `G`,
so the subsequence has pointwise vanishing defect but does not converge to `1`
at `s`, a contradiction.

**Item 2.**  Let `e_1, ..., e_d` be an orthonormal basis and `p_i` the
rank-one projection onto `e_i`.

*Boundary.*  For `X = phi(s) - 1`,
`[phi(s), p_i] = X p_i - p_i X`, so

```text
sum_i ||[phi(s), p_i]||_2^2
  <= 2 sum_i (||X p_i||_2^2 + ||p_i X||_2^2) = 4 ||X||_2^2 <= 4 eta(delta)^2,
```

using `sum_i tau(p_i X^* X p_i) = tau(X^* X)`.  This covers both the fine
clause for `S_Gamma` and the coarse clause for `S_G`, since `B_G = B_Gamma`.

*Gaps.*  Every corner `p_i M_d p_i` is one-dimensional, so every self-adjoint
`x` in it equals `tau_i(x) p_i`, and both Poincare inequalities hold with any
constant.

*Compressor transport.*  With `sigma_t = id`,
`sum_i ||phi(t) p_i phi(t)^* - p_i||_2^2 = sum_i ||[phi(t), p_i]||_2^2 <=
4 eta(delta)^2` for `t in {u, v}`, and trace ratios equal `1`.

*Remaining clauses.*  `tau(1 - p) = 0`, and nesting `B_G <= B_Gamma` is
equality.

**Item 3.**  Given any two one-level decompositions, discard them and use
the rank-one algebra of item 2 for both.

* The replacement changes the surviving projection by trace `0`.
* It adds total generator boundary at most `4 eta(delta)^2 -> 0`.
* The two algebras are nested (equal) and transported by `u, v` under the
  mass-weighted clause.
* All surviving blocks keep a positive gap, vacuously.

**Equivalences.**

* *Block decomposition.*  The reverse implication is
  `transported-gap-masa-kills-leavitt-hs-models`, part (C).
* *Block compatibility.*  Granting `hs-one-level-expander-block-decomposition`,
  the route `hs-expander-block-decomposition-from-one-level-and-compatibility`
  turns compatibility into the decomposition, and part (C) finishes.
