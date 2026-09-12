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

For the unitary-domain strengthening take `N=k^2`.  The `k` leaves equal to
one contribute `k`, and the equal populations of `i,-i` cancel, proving
`(RNS7)`.  After the stated opposite rotations, both imaginary populations
still cancel and every rotated leaf contributes real part
`-sin(epsilon)=-1/(k-1)`.  Since `N-k=k(k-1)`, this cancels the contribution
`k` exactly and proves `(RNS8)`.  The chord bound
`|exp(i epsilon)-1|=2 sin(epsilon/2)<=2 sin(epsilon)` gives `(RNS9)`.
Reusing the same exact proof and applying rooted soundness yields `(RNS10)`.
