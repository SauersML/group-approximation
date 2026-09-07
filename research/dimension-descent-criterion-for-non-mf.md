---
rg: 2
id: dimension-descent-criterion-for-non-mf
kind: claim
title: A dimension-reducing repair operation on visible models proves non-MF with no Kazhdan input
distinct_from:
  full-mf-radical-linear-relator-inequality: that is a global linear inequality equivalent to full MF radical, and gives no procedure; this is a sufficient condition of a different shape, a descent on the matrix dimension, and it is the operation rather than an inequality that has to be built.
  uniform-finite-mf-obstruction: that is a finite test with a positive threshold for one group, obtained by compactness; this asks for an operation transforming models and concludes by minimality of the dimension.
  canonical-swap-corners-have-no-dimension-descent: that computes the sharp padding cost of restoring one compressed actor and closes the compression route; this is the criterion such an operation would feed, and it does not require the new model to be a compression.
artifacts:
  - research/artifacts/dimension-descent-criterion-2026-09-07.md
---

Let `G` be countable with a nontrivial involution `z`, given as a word in a
generating tuple `s_1,...,s_k`, and let `R` be a finite set of relations of
`G` with `z^2 in R`.  Write

```text
delta(U) = max_(r in R) ||r(U) - I||_op.
```

Suppose there is `epsilon_0 > 0` such that for every `d` and every
`U in U(d)^k` with

```text
delta(U) < epsilon_0    and    ||z(U) - I|| >= 1
```

there is `V in U(d')^k` with `1 <= d' < d`, `delta(V) < epsilon_0` and
`||z(V) - I|| >= 1`.

Then `z` lies in the MF residual of `G`, so `G` is not MF.  If `z` normally
generates `G`, then `Res_MF(G) = G`.

No property (T) and no finite presentation are used.  The new tuple `V` is
unconstrained: it need not consist of compressions of the entries of `U`.
