---
rg: 2
id: kl-length-six-one-coincidence-weight-proof
kind: route
title: Weight the coincident pair and both loops by one and the two light corners by zero
target: kl-length-six-one-coincidence-words-inject
requires: []
---

**Weights.** The word has six corners.
- `theta = 1` on the two loops and on the two heavy same-sign corners, the
  pair that closes the trivial 2-cycle.
- `theta = 0` on the two light same-sign corners.

So `sum theta = 4 = n - 2`, which is (WT1) with equality. All weights are
nonnegative.

**Light edges.**
- (F1) and (F3): the P-edges `g` and `h`, both `t^- -> t^+`.
- (F2): the P-edge `g` (`t^- -> t^+`) and the N-edge `n` (`t^+ -> t^-`).

In every pattern the light subgraph is one 2-cycle between `t^-` and `t^+`.
Its basic cycle has label `lambda` at `t^-` and `lambda'` at `t^+`:
- `g h^(-1)` through `Pg Ph^(-1)` in (F1) and (F3);
- `g n` through `Pg N` in (F2).

**Admissible cycles.** An admissible cycle is a cyclically reduced closed path
in the star graph whose label is trivial in `G`. Count traversals of
weight-one corners with multiplicity. A cycle with two or more such traversals
has weight at least two. Otherwise:

*No weight-one traversal.* The cyclically reduced closed paths in the light
2-cycle are its nonzero powers, with labels `lambda^k` or `lambda'^k`,
`k != 0`. Condition 1 makes them nontrivial.

*Exactly one weight-one traversal `E`.* Reversing a cycle inverts its label,
so we may traverse `E` forward. Rotate the cycle to start at `E`. The rest is
a reduced path of light edges from the end of `E` back to its start. A light
path between the two vertices alternates the two light edges, since
traversing one light edge twice in succession, in opposite directions, is a
backtrack.

- **`E` a loop.**
  - At `t^-`, the light path is a closed path at `t^-`, with label in
    `<lambda>` (possibly empty). The cycle label `y lambda^k` is trivial only
    if `y` is in `<lambda>`.
  - At `t^+`, likewise, it is trivial only if `x` is in `<lambda'>`.
  - Condition 3 excludes both.
- **(F1) and (F3), `E` the heavy P-edge `Pu` (`t^- -> t^+`, label `u`).** The
  light path from `t^+` to `t^-` is one of:
  - `(Pg^(-1) Ph)^m Pg^(-1)`, with label `(g^(-1) h)^m g^(-1) = g^(-1) lambda^(-m)`;
  - `(Ph^(-1) Pg)^m Ph^(-1)`, with label `(h^(-1) g)^m h^(-1) = h^(-1) lambda^m`.

  The cycle labels are `u g^(-1) lambda^(-m)` and `u h^(-1) lambda^m`. Since
  `g = lambda h`, the coset `<lambda> g` equals `<lambda> h`, so either label is
  trivial only if `kappa = u h^(-1)` is in `<lambda>`. Condition 2 excludes
  this. In (F3) both heavy corners are such P-edges.
- **(F1), `E` the heavy N-edge `N` (`t^+ -> t^-`, label `u^(-1)`).** The light
  path from `t^-` to `t^+` is one of:
  - `(Pg Ph^(-1))^m Pg`, with label `lambda^m g`;
  - `(Ph Pg^(-1))^m Ph`, with label `lambda^(-m) h`.

  The cycle label `u^(-1) lambda^m g` or `u^(-1) lambda^(-m) h` is trivial only
  if `u` is in `<lambda> g = <lambda> h`. That is equivalent to `kappa` in
  `<lambda>`, excluded.
- **(F2), `E` either heavy P-edge `Pu`.** The light path from `t^+` to `t^-` is
  one of:
  - `(N Pg)^m N`, with label `(n g)^m n = n lambda^m`;
  - `(Pg^(-1) N^(-1))^m Pg^(-1)`, with label `(g^(-1) n^(-1))^m g^(-1) = g^(-1) lambda^(-m)`.

  The cycle labels are `u n lambda^m` and `u g^(-1) lambda^(-m)`. Since
  `n = g^(-1) lambda`, we have `u n = u g^(-1) lambda`, so either label is
  trivial only if `kappa = u n` is in `<lambda>`. Excluded.

Every admissible cycle has weight at least two, which is (WT2).

**Curvature.** The derivation is word for word the section "Curvature:
injectivity and diagrammatic reducibility" of
`kl-four-same-sign-corner-words-weight-proof`. That argument uses only four
things:
- (WT1) and (WT2);
- `theta >= 0`;
- orientability, from `deg_t(w) != 0`;
- that `w` is not a proper power.

So `G` injects into `(G * <t>)/<<w>>`, and every reduced spherical picture is
empty.

**Not verified at source.** The same two gaps as that route:
- the weight conditions come from the Ahmad--Al-Mulla--Edjvet restatement of
  Bogley--Pride;
- the relative van Kampen lemma and the dipole step are standard picture
  calculus, not re-read.
