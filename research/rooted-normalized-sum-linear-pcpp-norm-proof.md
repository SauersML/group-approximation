---
rg: 2
id: rooted-normalized-sum-linear-pcpp-norm-proof
kind: route
title: Reuse one exact auxiliary proof after deleting the vanishing-norm leaf boundary
target: rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm
requires:
  - uniform-linear-pcpp-tensorizes-to-amitsur-hs
---

Choose the valid boundary `(RNS3)`.  Its normalized sum is one, so exact
kernel projection in `(LPA3)` supplies `z_good`.  Keep that same auxiliary
proof and delete all leaves.  The checker residual changes by exactly the
image under `D_N` of the deleted leaf vector; its boundary norm is
`N^(-1/2)`.  Rooted soundness nevertheless lower-bounds the new residual by
`kappa_N`, because the root remains one and the normalized leaf sum becomes
zero.  The definition of operator norm therefore gives
`kappa_N<=||D_N||/sqrt(N)`, which is `(RNS6)`.

