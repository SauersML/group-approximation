---
rg: 2
id: kl-three-coincidence-residue-weight-proof
kind: route
title: Weight the heavy triple by one and the light corner by zero, and split the last unit between the loops
target: kl-three-coincidence-residue-words-inject-with-room-for-loops
requires: []
---

Use the star graph of `kl-four-same-sign-corner-words-inject`:
- a P-corner is an edge `t^- -> t^+`;
- an N-corner is an edge `t^+ -> t^-`;
- `y` is a loop at `t^-`, and `x` a loop at `t^+`.

**Heavy triple and light corner.**
- In the four `+++++-` shapes, the three P-labels `1` pairwise close
  `P_i P_j^(-1)` with label `1`.
- In `(1,1,g)` and `(g,1,1)`, the two P-labels `1` and the N-label `1` do:
  `P_i P_j^(-1)` has label `1`, and `P_i N` has label `a_i n = 1`.
- In `(g,g,g)`, the three P-labels `g` do. There the N-edge is light, since
  `P_i N` has label `g != 1`.

The light corner is the P-edge labelled `g` in the P-light shapes, and the
N-edge labelled `1` in `(g,g,g)`.

**Weights.** Put `theta = 1` on the heavy triple and `theta = 0` on the light
corner. Put `theta(y) = alpha` and `theta(x) = 1 - alpha`. Then
`sum theta = 4 = n - 2`, which is (WT1) with equality, and every weight is
nonnegative.

**Shape of an admissible cycle.** Let an admissible cycle make `2m` same-sign
steps, `h` of them on the heavy triple and `l` on the light corner, counted with
multiplicity. The steps alternate between steps into `t^+` and steps into
`t^-`. After a step into `t^+` the cycle runs a power `x^i`, and after a step
into `t^-` a power `y^j`, possibly zero. Two consecutive light steps traverse
the one light edge in opposite directions, so the power between them is
nonzero; otherwise the cycle backtracks. The weight is `h`, plus `alpha` times
the total `|j|`, plus `1 - alpha` times the total `|i|`.

**Labels of steps.**
- P-light shapes: every heavy step has label `1`. The light step into `t^+` has
  label `g`, and the light step into `t^-` has label `g^(-1)`.
- `(g,g,g)`: a heavy step into `t^+` has label `g`, and into `t^-` has label
  `g^(-1)`. Both light steps have label `1`.

**(WT2), case by case.**
- **`h >= 2`.** The weight is at least two.
- **`m = 0`.** The cycle is `y^j` or `x^i`, where `j` or `i` is a nonzero
  multiple of the order. Its weight is `alpha |j| >= alpha k_y >= 2`, or
  `(1 - alpha)|i| >= (1 - alpha) k_x >= 2`. A loop of infinite order has no such
  cycle.
- **`m = 1`, `h = 1`, `l = 1`.** Up to rotation and inversion the cycle is
  `e_+ x^i e_- y^j`, with one step heavy and one light. Its label is
  `g x^i y^j` or `x^i g^(-1) y^j`, in both shape families. It is trivial exactly
  when `g = y^(-j) x^(-i)` or `g = y^j x^i`. The weight is
  `1 + alpha |j| + (1 - alpha)|i|`, below two exactly when
  `alpha |j| + (1 - alpha)|i| < 1`. That set of `(i, j)` is closed under
  `(i, j) -> (-i, -j)`, so (C1) excludes every admissible cycle of weight below two.
- **`m = 1`, `h = 0`, `l = 2`.** Both powers are nonzero. The label is
  `g x^i g^(-1) y^j` in the P-light shapes and `x^i y^j` in `(g,g,g)`, and the
  weight is `alpha |j| + (1 - alpha)|i|`. So (C2), applied to `(i, -j)`,
  excludes every admissible cycle of weight below two.
- **`m >= 2`, `h <= 1`.** There are `2m` junctions between consecutive steps:
  `m` at `t^+` and `m` at `t^-`. The heavy step touches at most one junction on
  each side, so at least `m - 1` junctions at `t^+` and `m - 1` at `t^-` join two
  light steps and carry nonzero powers.
  - If `h = 1`, the weight is at least `1 + (m - 1)(alpha + 1 - alpha) >= 2`.
  - If `h = 0`, every junction joins two light steps, and the weight is at least
    `m(alpha + 1 - alpha) = m >= 2`.

Every admissible cycle has weight at least two, which is (WT2).

**Curvature.** The section "Curvature: injectivity and diagrammatic
reducibility" of `kl-four-same-sign-corner-words-weight-proof` uses only four
facts, all of which hold here:
- (WT1) and (WT2);
- `theta >= 0`;
- orientability, from `deg_t(w) != 0`;
- `w` is not a proper power.

So `G -> (G * <t>)/<<w>>` is injective, and every reduced spherical picture is
empty.

**Corollaries.**
- **`alpha = 1`, `k_x = infinity`.** (C1) reads `g != x^i` for every `i`.
  (C2) concerns `j = +-1` and `i != 0`; a conjugate of `x^i`, or `x^i` itself,
  has infinite order, while `y^(+-1)` has finite order.
- **`alpha = 1/2`, `k_y, k_x >= 4`.** (C1) is `|i| + |j| <= 1`, i.e.
  `g != 1, x^(+-1), y^(+-1)`. (C2) is `|i| + |j| <= 3` with `i, j != 0`.
- **No `alpha`.** Existence of `alpha` is `2/k_y <= 1 - 2/k_x`.

**Two-pair shapes.** Each disjoint heavy pair needs total weight at least two
on its own 2-cycle, so the same-sign corners take the whole budget four. A
torsion loop `y` then has `theta(y) = 0`, and `y^(k_y)` is an admissible cycle
of weight zero.

**Not verified at source.** The two gaps of
`kl-four-same-sign-corner-words-weight-proof` remain:
- the weight conditions come from the Ahmad--Al-Mulla--Edjvet restatement of
  Bogley--Pride;
- the relative van Kampen and dipole steps are standard picture calculus, not
  re-read.
