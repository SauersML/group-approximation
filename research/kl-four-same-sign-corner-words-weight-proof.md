---
rg: 2
id: kl-four-same-sign-corner-words-weight-proof
kind: route
title: Weight every loop by one and every same-sign edge by (e-2)/e
target: kl-four-same-sign-corner-words-inject
requires: []
---

**Weight test.** This is Bogley--Pride, *Aspherical relative presentations*,
Proc. Edinburgh Math. Soc. 35 (1992), Section 2.2, in the form used by
`kl-unit-exponent-words-free-corners-proof`. Suppose a nonnegative weight `theta`
on the edges of the star graph satisfies:
- (WT1) `sum over corners of (1 - theta) >= 2` for the relator;
- (WT2) every admissible cycle has weight at least two.

An admissible cycle is a cyclically reduced closed path whose label is `1` in
`G`; repeated edges are allowed. Under (WT1) and (WT2) the orientable relative
presentation is aspherical, and an aspherical relative presentation injects
its coefficient group. The relator `w` is orientable because
`deg_t(w^(-1)) = -m != m`.

**Weights.** Let `n` be the number of corners, `s` the number of loops and
`e = n - s` the number of same-sign edges. Put `theta = 1` on every loop and
`theta = beta = (e-2)/e` on every edge of `Theta`. Then
`sum theta = s + e - 2 = n - 2`, which is (WT1) with equality.

**Short labels.** Reduced closed paths of length two in `Theta` have the
following labels.
- At `t^-`:
  - two P-edges give `g g'^(-1)`;
  - a P-edge then an N-edge gives `g h`.
- At `t^+`:
  - two N-edges give `h h'^(-1)`;
  - an N-edge then a P-edge gives `h g`, which is conjugate to `g h`.

The two edges are distinct corners, since backtracking is not reduced. So
(D) is exactly the nontriviality of these labels.

**Admissible cycles.** `Theta` is bipartite on `{t^-}` and `{t^+}`, so every
closed path in `Theta` has even length. Let an admissible cycle traverse `k`
loops and `ell` edges of `Theta`. Its weight is `k + ell beta`.

- **k >= 2.** The weight is at least two.
- **k = 1.** Rotate the cycle to begin with its loop `x` at `v`. The rest is
  a closed path at `v` in `Theta` of even length `ell`.
  - If `ell = 0`, the label is `x != 1`, so the cycle is not admissible.
  - If `ell >= 2`, the weight is at least `1 + 2(e-2)/e`, and this is at
    least two exactly when `e >= 4`.
  - For `e = 3`, a cycle with `ell = 2` would make `x^(-1)` the label of a
    reduced closed path of length two at `v`. That set of labels is closed
    under inversion, so (A2) excludes the cycle. A cycle with `ell >= 4` has
    weight at least `7/3`.
- **k = 0.** The cycle is a nonempty cyclically reduced closed path in
  `Theta`, with weight `ell beta`.
  - For `e >= 4`: `ell = 2` is excluded by (D), and `ell >= 4` gives weight
    at least `4(e-2)/e >= 2`.
  - For `e = 3`, where `beta = 1/3`: (D) and (D4) exclude `ell = 2` and
    `ell = 4`, and `ell >= 6` gives weight at least two.

Every admissible cycle has weight at least two, so the weight test gives
asphericity and injectivity of `G`.

**Sharpness of the budget.** With loops at weight one, which the double
traversal of an involution loop forces, (WT1) leaves exactly `e - 2` for
`Theta`. A trivial 2-cycle then needs a pair of edges of total weight two.
That is why coincident same-sign labels are the residue.
