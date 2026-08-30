---
rg: 2
id: stw77-near-duplicate-fd-blocks-merge
kind: claim
title: Near-duplicate finite-dimensional blocks merge before central splitting
distinct_from:
  stw77-fd-commutant-splitting-iff-proper-supports: that characterizes commutation with the whole chosen model; this first coarsens near-duplicate blocks for a fixed tuple.
  one-sided-fd-models-allow-finite-junk-corners: that exhibits a bad chosen model; this explains exactly when its finite junk is harmless.
---

Let `B` be unital and let

```text
D=direct_sum_(j=1)^r D_j subset B,   D_j isomorphic to M_(n_j),
```

be a unital finite-dimensional subalgebra. Partition the block indices into
clusters `C` such that `n_j=n_C` for `j in C`, and fix isomorphisms

```text
sigma_(C,j):M_(n_C)->D_j.
```

Choose a reference index `j_C in C`. Let `x_1,...,x_m in D`, write
`x_l^(j)` for the `D_j` coordinate, and suppose

```text
max_(C,j in C,l)
 ||sigma_(C,j)^(-1)(x_l^(j))
   -sigma_(C,j_C)^(-1)(x_l^(j_C))|| <= delta.
```

For a rank-one projection `e_C in M_(n_C)`, put

```text
p_C=sum_(j in C) sigma_(C,j)(e_C).
```

If every `p_C` is properly infinite in `B`, then there are isometries
`s_1,s_2 in B` with orthogonal ranges such that

```text
max_(l,t)||[s_t,x_l]|| <= 2 delta.
```

The hypothesis is independent of the chosen rank-one `e_C`. In particular,
a finite block is not an obstruction when it can be diagonally merged with
near-duplicate blocks whose aggregate rank-one support is properly infinite.
