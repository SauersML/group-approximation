---
rg: 2
id: kl-four-same-sign-corner-words-weight-proof
kind: route
title: Weight loops and heavy same-sign edges by one and light edges by (r-2)/r
target: kl-four-same-sign-corner-words-inject
requires: []
---

**Weight conditions.** Take a nonnegative weight `theta` on star-graph edges
satisfying two conditions.

- (WT1) `sum over corners of (1 - theta) >= 2` for the relator.
- (WT2) Every admissible cycle has weight at least two. An admissible cycle is
  a cyclically reduced closed path whose label is `1` in `G`. Repeated edges
  are allowed; the bounds below count them with multiplicity.

These are the conditions of the Bogley--Pride weight test (*Aspherical
relative presentations*, Proc. Edinburgh Math. Soc. 35 (1992), Section 2.2),
as used in `kl-unit-exponent-words-free-corners-proof`. The last section
derives the conclusion directly by curvature, so this route does not use
their theorem that aspherical relative presentations inject. `w` is orientable
because `deg_t(w^(-1)) = -m != m`.

**Weights.** Let `n` be the number of corners, `s` the number of loops,
`e = n - s` the number of same-sign edges, and `r` the number of light ones.

- `theta = 1` on loops and on heavy edges.
- `theta = beta = (r-2)/r` on light edges.

Then `sum theta = s + (e - r) + (r - 2) = n - 2`, which is (WT1) with equality.

**Short labels.** At `t^-`, a reduced closed path of length two has label
`g g'^(-1)` through two P-edges, and `g h` through a P-edge then an N-edge. At
`t^+` the labels are `h h'^(-1)` and `h g`, the latter conjugate to `g h`. The two
edges are distinct corners. By definition, such a path has trivial label only
when both of its edges are heavy.

**Admissible cycles.** `Theta` is bipartite on `{t^-}` and `{t^+}`, so every
closed path in `Theta` has even length. Let an admissible cycle traverse `k`
loops and `ell` edges of `Theta`, of which `j` are heavy.

- **k >= 2.** The weight is at least two.
- **k = 1.** Rotate the cycle to begin at its loop `x` at `v`. The rest is a
  closed path at `v` in `Theta` of even length `ell`.
  - `ell = 0` gives label `x != 1`, which is not admissible.
  - `ell >= 2` and `j >= 1` give weight at least two.
  - `j = 0` and `ell >= 2` give weight at least `1 + 2beta`, which is at least
    two iff `r >= 4`.
  - For `r = 3`, a light path with `ell = 2` would make `x^(-1)` a light
    length-two label at `v`. That set is closed under inversion, so (A2)
    excludes the cycle, and `ell >= 4` gives weight at least `1 + 4/3`.
- **k = 0.** The cycle is a nonempty cyclically reduced closed path in `Theta`.
  - `ell = 2`: the label is trivial only if both edges are heavy, so the
    weight is `2`.
  - `ell = 4`, `r >= 4`: the weight is at least `min(4 beta, 1 + 3 beta) >= 2`,
    because `beta >= 1/2`.
  - `ell = 4`, `r = 3`, `beta = 1/3`: (D4) excludes an all-light cycle, and a
    cycle with a heavy edge has weight at least `1 + 3 beta = 2`.
  - `ell >= 6`: the weight is at least `6 beta >= 2` for `r >= 3`.

Every admissible cycle has weight at least two, which is (WT2).

**Why heavy edges cost exactly one.** A trivial 2-cycle between two heavy
edges needs total weight two, and weight one on every heavy edge meets this
with no slack. It is also affordable: (WT1) charges each same-sign edge one
unit, so heavy edges at weight one take nothing from the light budget `r - 2`.

## Curvature: injectivity and diagrammatic reducibility

**Van Kampen.** Write `P = <G, t | w>`. By the relative van Kampen lemma
(Howie; Bogley--Pride), if `1 != g in G` dies in `G(P) = (G * <t>)/<<w>>`,
then some picture over `P` on a disc `D` has boundary label `g` and no arc
meeting `∂D`. Take one with the fewest discs and delete floating circles.

- It has no dipole, since cancelling one removes two discs.
- It has at least one disc, since a picture without discs has boundary
  label `1`.

**Regions are admissible.** The corners of each region read a closed path in
the star graph.

- A backtrack `e e^(-1)` between adjacent discs makes them mirror images
  across their shared arc, because `w` is orientable and not a proper power,
  so the edge `e` fixes the whole cyclic permutation. That is a dipole, so
  interior region paths are cyclically reduced.
- A simply connected interior region has label `1` in `G`, so its path is
  admissible.

**Count.** Cap `∂D` with a disc to get `S^2`. Discs, arcs and regions satisfy
`V - E + sum_f chi(f) = 2`, where `chi(f) = 2 - b_f` and `b_f` counts the
boundary components of the region. At a corner with star-graph edge `e` put
angle `alpha = pi(1 - theta(e))`, and set

```text
kappa(v) = 2 pi - sum_(corners at v) alpha,
kappa(f) = 2 pi chi(f) - sum_(corners at f) (pi - alpha).
```

There are `2E` corners, so `sum kappa = 4 pi`. On the other hand:

- each disc carries the `n` corners of `w`, so
  `kappa(v) = 2pi - pi sum (1 - theta) = 0` by (WT1);
- a simply connected interior region has `kappa = 2pi - pi sum theta <= 0` by
  (WT2);
- a region with `b_f >= 2` has `kappa <= 0`, because `theta >= 0`;
- the region containing the cap has `kappa <= 2pi`, because `theta >= 0`.

So `sum kappa <= 2pi < 4pi`, a contradiction, and `G -> G(P)` is injective. A
reduced spherical picture with a disc has no cap region, so the same count
gives `sum kappa <= 0 < 4pi`. Hence every reduced spherical picture is empty.

**Not verified at source.**

- The weight conditions are taken from the verbatim restatement in
  Ahmad--Al-Mulla--Edjvet, arXiv:1604.00163v2 (J. Algebra Appl. 16 (2017)).
  Bogley--Pride Section 2.2 was not reached.
- The relative van Kampen lemma and the dipole step are standard picture
  calculus. They were not re-read in Howie or Bogley--Pride.
