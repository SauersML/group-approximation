---
rg: 2
id: square-zero-near-conjugacy-proof
kind: route
title: Prune the common length-two Jordan chains and conjugate only the discarded quotient
target: square-zero-near-conjugacy-in-rank
requires: []
---

The subspace `(SZC3)` has codimension `c<=2e` and is invariant for both
square-zero maps, which agree there.  Its common image loses at most `c`
dimensions from the rank-`r` ambient images.  Also
`dim(im A+im B)<=r+e`, since the quotient of `im B` modulo `im A` is an image
of `B-A`.  These two estimates produce at least `r-c` common length-two
chains and at least `n-2r-c-e` common length-one chains.  Their sum is a
direct summand for both maps of codimension at most `3c+e<=8e`.
Jordan-block cancellation gives isomorphic complements because the two full
maps have equal rank.  Use the identity on the common summand and any module
isomorphism on the complements.
