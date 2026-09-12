---
rg: 2
id: stw77-zero-models-admit-proper-block-clustering
kind: claim
title: Zero-color models admit proper-support clustering of near-duplicate blocks
---

Let `phi:A->B` satisfy the hypotheses of STW LXXVII and have nuclear
dimension zero. For every finite set of contractions `a_1,...,a_m in A` and
every `eta>0`, there are

1. a unital finite-dimensional algebra `D=direct_sum_j D_j subset B`;
2. elements `x_l in D` with `||x_l-phi(a_l)||<eta`;
3. a partition of the blocks into clusters of equal matrix size, with
   isomorphisms and reference blocks as in
   `stw77-near-duplicate-fd-blocks-merge`;

such that the coordinate variation of every `x_l` inside every cluster is
less than `eta`, and the aggregate rank-one support of every cluster is
properly infinite in `B`.

## Attempts

- Singleton clusters recover the already established proper-support model
  criterion. The point of the present statement is that individual finite
  summands may be retained when their tuple representations can be merged.
- The finite corner in `one-sided-fd-models-allow-finite-junk-corners` is not
  a counterexample: on each prescribed finite set, the `ev_(t_n)` and `ev_0`
  scalar blocks are arbitrarily close and their diagonal aggregate support is
  the properly infinite unit.
- `stw77-z-o2-map-defeats-projection-return` is also not a counterexample.
  No model projection is required to approach the range, and every nonzero
  projection of `O_2` is already properly infinite.
- The unresolved step is to use proper infiniteness of the image to show that
  every representation type needed by a finite tuple has properly infinite
  aggregate support. If equal-size diagonal clustering is too rigid, the
  required replacement is a finite-dimensional coarsening with the same two
  quantitative properties; projection return is not available.
