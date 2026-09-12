---
rg: 2
id: iwahori-edge-has-no-common-finite-index-normal-core
kind: claim
title: The two Iwahori vertices have no common finite-index normal edge core
distinct_from:
  finite-index-double-theorem-misses-iwahori-twist: that proves the edge isomorphism does not extend to a vertex automorphism; this proves that shrinking the edge cannot turn both inclusions into finite-group extensions over one common normal base.
  homogeneous-k-orbit-factor-has-no-finite-a-refinement: that excludes a common finite equivariant refinement of the K-orbit partition on the compact quotient; this is the abstract Bass--Serre subgroup obstruction inside SL2(Z[1/p]).
  iwahori-local-global-defect-question: that asks for flexible normalized-HS repair of almost-compatible vertex representations; this only excludes an exact finite-depth reduction through a common normal subgroup.
---

Let

```text
A = SL_2(Z[1/p]) = C *_D C',
C = SL_2(Z),  C' = g C g^-1,
D = C cap C',  g = diag(p,1).
```

There is no infinite subgroup `E <= D` which is finite-index in `D` and
normal in both `C` and `C'`.  Since `D` has finite index `p+1` in each
vertex, the two finite-index inclusions cannot be reduced, after shrinking
the edge, to finite-group extensions of one shared normal crossed-product
base.

Proof: `normal-subgroup-theorem-kills-a-common-iwahori-core`.

**Consequence for the homogeneous-quotient AFP.**  In `(HQ5)`, passing from
`B=L^infinity(X) rtimes D` to a subgroup crossed product
`L^infinity(X) rtimes E` can never make that algebra simultaneously normal
under both vertex crossed products with finite quotient.  Thus the standard
finite-group-crossed-product/Morita reduction cannot prove Connes
embeddability of `N_1 *_B N_2`.  This is an exact-model obstruction only;
it does not rule out compatible embeddings in a tracial matrix
ultraproduct.

