---
rg: 2
id: kl-four-same-sign-corner-words-weight-proof
kind: route
title: Weight loops and heavy same-sign edges by one and light edges by (r-2)/r
target: kl-four-same-sign-corner-words-inject
requires: []
---

**Weight test.** Bogley--Pride, *Aspherical relative presentations*,
Proc. Edinburgh Math. Soc. 35 (1992), Section 2.2, in the form used by
`kl-unit-exponent-words-free-corners-proof`. Take a nonnegative weight
`theta` on star-graph edges satisfying:

- (WT1) `sum over corners of (1 - theta) >= 2` for the relator;
- (WT2) every admissible cycle has weight at least two. An admissible cycle is
  a cyclically reduced closed path whose label is `1` in `G`, and repeated
  edges are allowed.

Then the orientable relative presentation is aspherical, and aspherical
relative presentations inject their coefficient group. `w` is orientable
because `deg_t(w^(-1)) = -m != m`.

**Weights.** Let `n` be the number of corners, `s` the number of loops,
`e = n - s` the number of same-sign edges, and `r` the number of light ones.

- `theta = 1` on loops and on heavy edges.
- `theta = beta = (r-2)/r` on light edges.

Then `sum theta = s + (e - r) + (r - 2) = n - 2`, which is (WT1) with equality.

**Short labels.** At `t^-`, a reduced closed path of length two through two
P-edges has label `g g'^(-1)`, and through a P-edge then an N-edge `g h`. At
`t^+` the labels are `h h'^(-1)` and `h g`, the latter conjugate to `g h`. The two
edges are distinct corners. By definition, such a path has trivial label only
when both of its edges are heavy.

**Admissible cycles.** `Theta` is bipartite on `{t^-}` and `{t^+}`, so every
closed path in `Theta` has even length. Let an admissible cycle traverse `k`
loops and `ell` edges of `Theta`, of which `j` are heavy.

- **k >= 2.** The weight is at least two.
- **k = 1.** Rotate the cycle to begin at its loop `x` at `v`. The rest is a
  closed path at `v` in `Theta` of even length `ell`.
  - `ell = 0` gives label `x != 1`, so the cycle is not admissible.
  - If `ell >= 2` and `j >= 1`, the weight is at least `2`.
  - If `j = 0` and `ell >= 2`, the weight is at least `1 + 2beta`, which is at
    least two iff `r >= 4`.
  - For `r = 3`, a light path with `ell = 2` would make `x^(-1)` a light
    length-two label at `v`, and this set is closed under inversion. So (A2)
    excludes the cycle, and `ell >= 4` gives `1 + 4/3`.
- **k = 0.** The cycle is a nonempty cyclically reduced closed path in `Theta`.
  - **`ell = 2`.** The label is trivial only if both edges are heavy, giving
    weight `2`.
  - **`ell = 4`, `r >= 4`.** The weight is at least `min(4 beta, 1 + 3 beta) >= 2`,
    because `beta >= 1/2`.
  - **`ell = 4`, `r = 3`, where `beta = 1/3`.** An all-light cycle is excluded
    by (D4). A cycle with at least one heavy edge has weight at least
    `1 + 3 beta = 2`.
  - **`ell >= 6`.** The weight is at least `6 beta >= 2` for `r >= 3`.

Every admissible cycle has weight at least two, so the weight test gives
asphericity and injectivity of `G`.

**Why heavy edges cost exactly one.** A trivial 2-cycle between two heavy
edges needs total weight two. Weight one on every heavy edge meets this with
no slack. It is also affordable: (WT1) charges each same-sign edge one unit,
so heavy edges at weight one take nothing from the light budget `r - 2`.
