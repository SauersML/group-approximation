---
rg: 2
id: kl-relative-weight-test-gives-injectivity
kind: claim
title: A nonsingular one-variable word that passes the star-graph weight test injects its coefficient group
distinct_from:
  kl-four-same-sign-corner-words-inject: that proves the weight test for one explicit weight (one on loops and heavy edges, (r-2)/r on light edges) under coincidence hypotheses; this is the general implication from any weight passing (WT1) and (WT2) to injectivity, with no hypothesis on the labels.
  kl-unit-exponent-words-inject-when-same-sign-corners-are-free: that is one explicit weight (loops one, same-sign edges zero) under a freeness hypothesis; this takes the weight as input.
  leavitt-paired-quotient-passes-relative-weight-test: that verifies the test for one Leavitt word; this is the implication a verified test gives, over every group.
  block-weight-matrix-test-lot-presentations-are-dr: that is the Barmak--Minian I-test for absolute presentations; this is the relative test for one relator over an arbitrary coefficient group.
  aspherical-adjunction-has-zero-schur-kernel: that starts from asphericity of the relative 2-complex; this derives injectivity of the coefficient group directly from a weight by curvature.
---

Let `G` be any group and

```text
w = g_0 t^(e_0) g_1 t^(e_1) ... g_(n-1) t^(e_(n-1))  in  G * <t>,
```

with every `e_i = +-1` (powers of `t` split into single letters, so a corner
inside a power carries the label `1`). Assume:
- `w` is cyclically reduced: `g_i != 1` whenever `e_(i-1) != e_i` (indices mod `n`);
- `w` is not a proper power in `G * <t>`;
- `deg_t(w) = sum e_i != 0`.

**Star graph.** Corner `i` sits between `t^(e_(i-1))` and `t^(e_i)` and carries
the label `g_i`. It is an edge `t^(-e_(i-1)) -> t^(e_i)` on the two vertices
`t^-`, `t^+`, as in `kl-unit-exponent-words-inject-when-same-sign-corners-are-free`.
A path may traverse an edge forwards (reading `g_i`) or backwards (reading
`g_i^(-1)`). The label of a path is the product of what it reads, in order.
A closed path is *cyclically reduced* if no step is followed, cyclically, by
the same edge traversed the other way. It is *admissible* if its label is `1`
in `G`.

**The claim.** Suppose `theta : {0, ..., n-1} -> [0, infinity)` satisfies
- (WT1) `sum_i (1 - theta_i) >= 2`, and
- (WT2) every admissible cyclically reduced closed path has weight at least
  `2`, where the weight counts each traversal of edge `i` as `theta_i`
  (repeated edges counted with multiplicity).

Then `G -> (G * <t>)/<<w>>` is injective, and every reduced spherical picture
over `<G, t | w>` is empty.
