---
rg: 2
id: fpbs-lossless-move-comparison-fails-marginal-transfer
kind: claim
title: The lossless two-path comparison for one product move keeps the clusters but not the threshold, fails on Z^2 to the triangular lattice, and even where valid keeps the exponent-2 window
distinct_from:
  fpbs-generating-set-threshold-comparison: that proves the power-map inequalities by splitting each old edge into M independent copies; this studies the comparison with no splitting, refutes its marginal form on Z^2, and bounds what it could gain over the power map by the factor N M^2.
  fpbs-gap-survives-product-generator-moves: that is the move-invariance claim, still OPEN; this kills one class of proof attempts for it, the lossless comparison recorded there as its second attempt, and pins where that class dies.
artifacts:
  - experiments/lossless-move-calibration-2026-09-17/thresholds.py
  - experiments/lossless-move-calibration-2026-09-17/tree_of_triangles_check.py
---

**ESTABLISHED.** Proof in `fpbs-lossless-move-comparison-fails-marginal-transfer-proof`.

**Setting.** `Gamma` is finitely generated, `S` is finite symmetric with `e ∉ S`,
`t = uv` with `u, v ∈ S` and `t ∉ S ∪ {e}`, and `T = S ∪ {t, t^{-1}}`. Let
`N >= 1` be the number of pairwise edge-disjoint two-step `S`-paths from `e` to
`t` that we fix (at least one, `e -> u -> uv`). Put

```text
m_N(p) = 1 - (1 - p^2)^N.
```

**The lossless two-path process.** For `omega ~` Bernoulli(`p`) on the edges of
`Cay(Gamma,S)`, let `omega^` on the edges of `Cay(Gamma,T)` copy `omega` on the
old edges and open `{x, xt}` iff one of the `N` translated paths from `x` to `xt`
is `omega`-open. So `omega^` is a `Gamma`-equivariant, increasing, finite-range
block factor of Bernoulli(`p`). Its marginals are `p` on old edges and `m_N(p)` on
new edges.

**Theorem A (cluster identity).** Every realization of `omega^` has exactly the
same vertex clusters as `omega`. In particular, `omega^` has an infinite cluster
iff `omega` does.

**Theorem B (the marginal form is false).** Consider the lossless inequality

```text
(LL)   p_c(Cay(Gamma,S)) <= max( p_c(T), m_N^{-1}(p_c(T)) ),   p_c(T) = p_c(Cay(Gamma,T)).
```

It is what a lossless proof would give. Suppose every such process whose
marginals all exceed `p_c(T)` percolated. At any `p` with `min(p, m_N(p))`
above `p_c(T)`, `omega^` would then percolate, so `omega` would too, by
Theorem A, and `p >= p_c(S)`. (LL) fails for
`Gamma = Z^2`, `S = {±e_1, ±e_2}`, `t = e_1 + e_2`, `N = 2`, where
`Cay(Gamma,T)` is the triangular lattice:

- `max(p_c(tri), m_2^{-1}(p_c(tri))) = 0.438291...`, while `p_c(Z^2) = 1/2`;
- for every `p ∈ (0.438292, 1/2)`, `omega^` on the triangular lattice is
  invariant, ergodic, finite-range dependent and increasing. All its marginals are at least
  `m_2(p) > 2 sin(pi/18) = p_c(tri)`, yet it has no infinite cluster a.s. For
  example, at `p = 0.44` the marginals are `0.44` and `0.349719 > 0.347296`.

So "an invariant, increasing, finite-range factor of Bernoulli percolation whose
marginals exceed `p_c(T)` percolates on `Cay(Gamma,T)`" is false. Any valid
lossless argument must use more of the structure of `omega^` than its marginals,
its dependence range and its monotonicity. The established power map gives
`p_c(Z^2) <= phi^{-1}(p_c(tri)) = 0.8313...`, and the true value `1/2` lies
between the two predictions.

**Theorem C (exponent ceiling of the class).** Let `M` be the multiplicity in
`fpbs-generating-set-threshold-comparison` and `phi_M(p) = (1-(1-p)^{1/M})^2`.
For all `p ∈ [0,1]`:

```text
m_N(p) <= N p^2 <= N M^2 phi_M(p).
```

Suppose (LL) held for a Remove move `T -> S`. It would give `p_c(S) < p_u(S)`
only when `p_c(T) < p_u(T)` and `p_c(T) < m_N(p_u(T))`, since `m_N` is
increasing and `p_u(S) >= p_u(T)`. The power-map corollary already gives this
whenever `p_c(T) < phi_M(p_u(T))`. So the Remove steps that (LL) certifies and
the power map does not all satisfy

```text
phi_M(p_u(T)) <= p_c(T) < N M^2 phi_M(p_u(T)).
```

That is, the gain is at most the constant factor `N M^2` in the window, and the
exponent `2` in `p_c(T) ≲ p_u(T)^2` is unchanged. The uncovered band
`N p_u(T)^2 <= p_c(T) <= p_u(T)` is not touched.

**Where the class dies.** It dies at two points:

1. Turning marginals of the dependent comparison process into percolation, by
   Theorem B. The recorded death "dependent across new edges" is here sharpened
   to an explicit amenability-blind counterexample.
2. Even granted (LL), the Remove window keeps exponent 2, by Theorem C. So a
   lossless comparison built from length-2 paths cannot reach the residual
   counterexample band of `fpbs-gap-survives-product-generator-moves`, which is
   `p_c(T) <= p_u(T) ≲ sqrt(p_c(T)/N)`. The square-root loss comes from the path
   length `L = 2`, not from the splitting into `M` copies.

**Remark (not claimed).** On the nonamenable tree-like move
`Cay(F_2,{a,b}) -> Cay(F_2,{a,b,ab})`, (LL) holds with room to spare:
- `N = 1` and `p_c(T_4) = 1/3`;
- the Cayley graph of `{a,b,ab}` is the tree of triangles with three triangles
  per vertex, checked to radius 5 by `tree_of_triangles_check.py`;
- its `p_c` is the root `0.2140...` of `4(p + p^2 - p^3) = 1`, and
  `m_1^{-1}(0.2140) = 0.4626 >= 1/3`.

Whether (LL) holds for all moves on nonamenable groups is open, and by
Theorem C it would not decide the target anyway.
