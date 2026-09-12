---
rg: 2
id: kl-involution-loop-interior-light-label-curvature-proof
kind: route
title: Weight both involution loops by one half and move the curvature of each loop square across its two arcs
target: kl-involution-loop-residue-with-interior-light-label-injects
requires: []
---

**Star graph and weights.** Use the star graph of
`kl-four-same-sign-corner-words-inject`. The corners `c_0, ..., c_5` of `w` are
the P-edges `c_0, c_1, c_2, c_3` (labels `a_1, ..., a_4`, edges `t^- -> t^+`),
the loop `Y = c_4` at `t^-` and the loop `X = c_5` at `t^+`. In both shapes
`c_0` and `c_3` are heavy, and the light corner, labelled `g`, is `c_2` or `c_1`.
Put:
- `theta = 1` on the three heavy corners;
- `theta = 0` on the light corner;
- `theta(Y) = theta(X) = 1/2`.

Then `sum theta = 4 = n - 2`, which is (WT1) with equality.

**Curvature.** Follow the section "Curvature" of
`kl-four-same-sign-corner-words-weight-proof`: take a minimal picture on a disc
with boundary label `c != 1` in `G`, cap the boundary, and count angles
`pi (1 - theta)`, so that the total is `4 pi`. Every disc gets
`kappa = 2 pi - pi sum (1 - theta) = 0`. A region `f` gets

```text
kappa(f) = 2 pi chi(f) - pi W(f),     W(f) = sum of theta over its corners.
```

A simply connected interior region reads an admissible cycle.

**Claim A.** Write an admissible cycle with `2m` same-sign steps, `h` of them
heavy and `l` light, and the powers `X^i` and `Y^j` between steps, as in
`kl-three-coincidence-residue-weight-proof`. Every heavy label is `1`, a light
step into `t^+` has label `g`, and a light step into `t^-` has label `g^(-1)`.
Since `x^2 = y^2 = 1`, a power `X^i` has label `x` or `1` according to the
parity of `i`, and its weight is `|i|/2`. Then:
1. under (I1)-(I2), every admissible cycle has `W >= 2`, except the loop
   squares `Y^2` and `X^2` with `W = 1`;
2. under (I1)-(I4), every admissible cycle with at least one heavy step and at
   least one loop traversal has `W >= 5/2`.

*Proof.*
- **`m = 0`.** `Y^j` or `X^i` with `|j|` or `|i|` even and nonzero, so
  `W = |j|/2 >= 1`, with equality exactly for the squares. There is no heavy step.
- **`h >= 2`.** `W >= 2`, and `W >= 5/2` once a loop is traversed.
- **`m = 1`, `h = l = 1`.** The label is `g x^i y^j` or `x^i g^(-1) y^j`, and
  `W = 1 + (|i| + |j|)/2`.
  - `|i| + |j| = 0`: the label is `g^(+-1) != 1`.
  - `|i| + |j| = 1`: triviality means `g = x` or `g = y`, excluded by (I1).
  - `|i| = |j| = 1`: triviality means `g = y x`, excluded by (I3).
  - `(|i|, |j|) = (2, 0)` or `(0, 2)`: the label is `g^(+-1)`.

  So these cycles have `W >= 5/2`.
- **`m = 1`, `h = 0`, `l = 2`.** Both powers are nonzero, the label is
  `g x^i g^(-1) y^j`, and `W = (|i| + |j|)/2 >= 1`.
  - `W = 1`: `i`, `j` odd, and triviality is `g x g^(-1) = y`, excluded by (I2).
  - `W = 3/2`: one power is even, and the label is `y` or `g x g^(-1)`, nontrivial.

  So `W >= 2`, with no heavy step.
- **`m >= 2`, `h <= 1`.** By the junction count of
  `kl-three-coincidence-residue-weight-proof`, `W >= m >= 2` when `h = 0`, and
  `W >= 1 + (m - 1) >= 2` when `h = 1`. Equality with `h = 1` forces `m = 2`, the
  two light-light powers `+-1`, and zero powers at the two junctions touching the
  heavy step. Up to rotation and inversion the label is then
  `g^2 x g^(-1) y`, excluded by (I4). The other placement,
  `g^(-1) y g x g^(-1)`, is conjugate to its inverse.

**Positive regions.** By Claim A, apart from the boundary region, only
interior loop-square regions have positive curvature, and they have
`kappa = pi`. A loop square is a degree-two region between two discs of equal
orientation at their `Y` corners, or at their `X` corners. Opposite orientations
would make a dipole.

**Transfer.** Each interior loop square gives `pi/2` across each of its two arcs
to the region on the other side, and ends with `kappa = 0`. For positive discs:
- A `Y^2` region between `D_1` and `D_2` has arcs `(D_1, 4)-(D_2, 5)` and
  `(D_1, 5)-(D_2, 4)`. Tracing the faces, the region across the first arc contains
  the consecutive corners `c_3` of `D_1` and `X` of `D_2`, and across the second
  `c_3` of `D_2` and `X` of `D_1`.
- An `X^2` region has arcs `(D_1, 5)-(D_2, 0)` and `(D_1, 0)-(D_2, 5)`. The regions
  across them contain the consecutive corners `Y` of `D_1` and `c_0` of `D_2`,
  resp. `Y` of `D_2` and `c_0` of `D_1`.

Negative discs give the mirror pairs `(X^(-1), c_3^(-1))` and
`(c_0^(-1), Y^(-1))`.

So each transfer into a region `A` comes with a *transfer pair*: a corner `c_3`
or `c_0` and a loop corner of `A`, joined by the arc the transfer crosses. These
pairs are disjoint:
- a corner `c_3` pairs only through its arc `4`, and `c_0` only through its arc `0`;
- an `X` corner pairs only through its arc `5` with a `Y^2` region at the same
  disc, and a `Y` corner only through its arc `5` with an `X^2` region.

In both shapes `c_0` and `c_3` are heavy. So if `A` receives `k` transfers, it has
at least `k` heavy corners and `k` loop corners, and `W(A) >= 3k/2`.

**Count.**
- **`k = 0`.** `kappa(A) <= 0` for interior regions, by Claim A 1 or `chi <= 0`.
  The boundary region has `kappa <= 2 pi`.
- **`k >= 2`.** `kappa(A) + k pi/2 <= 2 pi - 3k pi/2 + k pi/2 = 2 pi - k pi <= 0`.
- **`k = 1`.** `A` has a heavy corner and a loop corner.
  - A simply connected interior `A` has `W >= 5/2` by Claim A 2, so its final
    curvature is at most `2 pi - 5 pi/2 + pi/2 = 0`.
  - With `chi(A) <= 0` it is at most `-3 pi/2 + pi/2 < 0`.
  - The boundary region stays at most `pi`.

The boundary region is never a loop square, since its label is `c != 1`. So the
total after transfer is at most `2 pi < 4 pi`, a contradiction, and
`G -> (G * <t>)/<<w>>` is injective. A reduced spherical picture has no boundary
region, so the same count gives total at most `0 < 4 pi`, and it is empty.

**Where the other shapes fail.** In `(1,1,1,g)` the corner `c_3` is light, and
in `(g,1,1,1)` the corner `c_0` is. A receiving region can then gain two
transfers from light-corner pairs while having no heavy corner, for instance
the region `g X^2 g^(-1) Y^2` of weight two.

**Not verified at source.** The two gaps of
`kl-four-same-sign-corner-words-weight-proof` remain:
- the weight conditions come from the Ahmad--Al-Mulla--Edjvet restatement of
  Bogley--Pride;
- the relative van Kampen and dipole steps are standard picture calculus, not
  re-read.
