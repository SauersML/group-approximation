---
rg: 2
id: kl-three-equal-residue-one-sided-weight-curvature-proof
kind: route
title: Put the whole loop weight on one loop and move the curvature of each power region of the other loop across its arcs
target: kl-three-equal-residue-shapes-inject-for-every-loop-order
requires: []
---

**Star graph and reading.** Use the star graph of
`kl-involution-loop-interior-light-label-curvature-proof`:
- the P-edges `c_0, ..., c_3` run `t^- -> t^+`, with labels `a_1, ..., a_4`;
- `Y = c_4` is a loop at `t^-`, and `X = c_5` a loop at `t^+`.

Arc `i` of a disc is its `i`-th `t`-letter, so corner `c_i` lies between arcs `i`
and `i + 1`. Reading the corners of a region counterclockwise gives a closed path
in the star graph:
- a corner of a positive disc is read forward, from arc `i` to arc `i + 1`;
- a corner of a negative disc is read backward, with inverted label.

So a step along a P-edge into `t^+` has label `a_i`, and into `t^-` label
`a_i^(-1)`.

**Part (b) from part (a).** The automorphism `t -> t^(-1)` of `G * <t>` fixes `G`.
It sends `w^(-1)` to a conjugate of

```text
w' = t a_4^(-1) t a_3^(-1) t a_2^(-1) t a_1^(-1) t x^(-1) t^(-1) y^(-1).
```

This is the same class with `(a_1, a_2, a_3, a_4, y, x)` replaced by
`(a_4^(-1), a_3^(-1), a_2^(-1), a_1^(-1), x^(-1), y^(-1))`.
- The normal closures match, so injectivity and spherical pictures transfer.
- `a_4 = 1` becomes `a'_1 = 1`, and `g' = g^(-1)`.
- (X1), (X2), (X3) for `w'` read `g^(-1)` not in `<y>`, `x^(-1)` not in
  `g^(-1) <y> g`, and `g^(-1)` not in `x^(-+1) <y>`. These are (Y1), (Y2), (Y3).

So it is enough to prove (a).

**Weights.** Put:
- `theta = 1` on the three heavy corners, including `c_0` (since `a_1 = 1`);
- `theta = 0` on the light corner;
- `theta(Y) = 1` and `theta(X) = 0`.

Then `sum theta = 4 = n - 2`. Follow the section "Curvature: injectivity and
diagrammatic reducibility" of `kl-four-same-sign-corner-words-weight-proof`:
- take a picture on a disc with boundary label `1 != c in G` and the fewest discs;
- cap the boundary, and put angle `pi (1 - theta)` at each corner, so that the
  total curvature is `4 pi`.

Every disc gets `kappa = 0`. A region `f` gets `kappa(f) = 2 pi chi(f) - pi W(f)`,
where `W(f)` is the sum of `theta` over its corners. Interior region paths are
cyclically reduced, since a backtrack is a dipole. Here `w` is orientable and not
a proper power: its `t`-exponent sum is `4`, and `+++++-` is no power of a shorter
sign pattern.

**Claim A'.** Write an admissible cycle with `2m` P-steps, `h` heavy and `l` light,
and powers `X^i` at the junctions at `t^+` and `Y^j` at the junctions at `t^-`.
Heavy labels are `1`, and light labels are `g^(+-1)`. So
`W = h + sum |j|`. Then:
1. under (X1)-(X2), every admissible cycle other than a power of `X` has `W >= 2`;
2. under (X3), every admissible cycle in which a `c_0`-step is adjacent to a
   `Y`-step has `W >= 3`.

*Proof.*
- **`m = 0`.** `Y^j` with `y^j = 1` has `|j| >= 2`, since `y != 1`. Powers of `X`
  are excepted in 1 and have no `c_0`-step.
- **`h >= 2`.** `W >= 2`, and `W >= 3` when a `Y`-step occurs.
- **`m = 1`, `h = l = 1`.** Up to rotation and inversion the label is
  `x^i g^(-1) y^j`, and `W = 1 + |j|`.
  - `j = 0`: triviality means `g in <x>`, excluded by (X1).
  - `|j| = 1`: triviality means `g = y^(+-1) x^i`, excluded by (X3).

  So `W >= 2`, and `W >= 3` whenever a `Y`-step occurs.
- **`m = 1`, `h = 0`.** Both steps run along the light corner, so both powers are
  nonzero. The label is `g x^i g^(-1) y^j`, and `W = |j|`. When `|j| = 1`,
  triviality means `y^(-+1) = g x^i g^(-1)`, excluded by (X2). So `W >= 2`, and
  there is no `c_0`-step.
- **`m >= 2`, `h <= 1`.** By the junction count of
  `kl-three-coincidence-residue-weight-proof`, at least `m - 1` of the `m`
  junctions at `t^-` join two light steps and carry nonzero powers.
  - For 1: `W >= h + (m - 1) >= 2` when `h = 1`, and `W >= m >= 2` when `h = 0`.
  - For 2: `c_0` is heavy, so `h = 1` and the heavy step is the `c_0`-step. Its
    own junction at `t^-` carries the adjacent `Y`-step, so all `m` junctions at
    `t^-` are nonzero, and `W >= 1 + m >= 3`.

**Positive regions.** Call a region an *`X`-region* if all its corners are `X`
corners. By Claim A' 1, the interior regions of positive curvature are the simply
connected `X`-regions, with `W = 0` and `kappa = 2 pi`. Each has degree `d >= 2`,
since `x != 1`, and there are none when `x` has infinite order.

Consecutive discs around an `X`-region have equal orientation. Otherwise the path
of the region contains `X X^(-1)`: the arc between the two discs joins arc `0` of
one to arc `0` of the other, which is a backtrack and so a dipole.

**Transfer.** Each interior simply connected `X`-region of degree `d` gives
`2 pi / d <= pi` across each of its arcs, and ends with `kappa = 0`. Take a
positive disc `D_1` in such a region. The arc leaving its `X` corner at arc `0`
ends at arc `5` of the next disc `D_2`. Reading counterclockwise, the region `A`
on the other side contains, consecutively:
- the `Y` corner of `D_2`, from arc `4` to arc `5`;
- the `c_0` corner of `D_1`, from arc `0` to arc `1`.

Negative discs give the mirror pair `(c_0^(-1), Y^(-1))`.

So each transfer into a region `A` comes with a *transfer pair*: a `c_0` corner
and a `Y` corner of `A`, adjacent across the arc the transfer crosses. In the cycle
of `A`, a `c_0`-step is then adjacent to a `Y`-step.
- A `c_0` corner pairs only through its arc `0`, and a `Y` corner only through its
  arc `5`. So the pairs of distinct transfers are disjoint.
- `A` has a `c_0` corner, so it is never an `X`-region.

If `A` receives `k` transfers, then `W(A) >= 2k`, since `theta(c_0) = theta(Y) = 1`.

**Count.**
- **`X`-regions.** A giving `X`-region ends at `0`. An interior `X`-region with
  `chi <= 0` has `kappa <= 0` and gives nothing. A boundary `X`-region has
  `kappa <= 2 pi` and receives nothing.
- **`k = 0`.**
  - An interior region has `kappa <= 0`, by Claim A' 1 or by `chi <= 0`.
  - The boundary region has `kappa <= 2 pi`.
- **`k >= 1`.** The final curvature is at most `2 pi chi(A) - 2k pi + k pi`.
  - An interior `A` with `chi(A) <= 0` ends below `0`.
  - A simply connected interior `A` with `k >= 2` ends at most at `(2 - k) pi <= 0`.
  - A simply connected interior `A` with `k = 1` has `W(A) >= 3` by Claim A' 2, and
    ends at most at `2 pi - 3 pi + pi = 0`.
  - The boundary region ends at most at `(2 - k) pi <= pi`.

So the total after transfer is at most `2 pi < 4 pi`, a contradiction, and
`G -> (G * <t>)/<<w>>` is injective. A reduced spherical picture has no boundary
region, so the same count gives total at most `0 < 4 pi`, and it is empty.

**Cross-check.** `research/artifacts/kl-residue-picture-census/one_sided_weight_check.py`
enumerates reduced closed star-graph paths of length at most ten and weight
below three. Labels live in `F(g) * C_(k_x)(x) * C_(k_y)(y)`, with
`(k_x, k_y) = (2,2), (3,3), (2,3)`. It runs each of the three shapes of (a) under
the `X`-scheme, and each of the three shapes of (b) under the mirror `Y`-scheme.

In all eighteen runs, recorded in `one-sided-weight-output-2026-09-12.txt`:
- no trivial-label cycle has `W < 2` unless it is a power of the zero-weight loop;
- no trivial-label cycle with a receiver-adjacent loop step has `W < 3`.

At orders `(2,3)`, apart from `g`, `x` and `y` alone, the nontrivial labels it
lists are exactly the relations that (X1)-(X3), resp. (Y1)-(Y3), exclude. It ran
on MSI.

**Not verified at source.** The relative van Kampen lemma and the dipole step
are used as in `kl-four-same-sign-corner-words-weight-proof`. They are standard
picture calculus, not re-read in Howie or Bogley--Pride. No weight test is
imported: the count above is done directly.
