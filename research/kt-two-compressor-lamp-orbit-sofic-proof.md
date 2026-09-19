---
rg: 2
id: kt-two-compressor-lamp-orbit-sofic-proof
kind: route
title: Identify the external orbit with SL3Z and separate finite lamp supports
target: kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath
requires:
  - kt-two-positive-compressors-generate-full-obstruction
  - kun-thom-nonsofic-wreath
---

The explicit generator calculation gives `<A,B>=SL_3(Z)`.  The external
factor intersects `Gamma` trivially, so its orbit of `Gamma` in `G/Gamma` is
the left regular orbit.  Residual finiteness of the Kun--Thom actor passes to
this subgroup.  To separate a finite binary lamp support, take a finite
quotient injective on the support and its pairwise differences and push the
lamp function along quotient fibers.  This proves residual finiteness of the
regular restricted wreath and supplies canonical permutation models of all
`A,B` cylinders and mixed traces.  Since those models already have an
actor-normalized cylinder masa, any contradiction using the full pair must
consume mixed transported `Gamma`-stabilizer data.
