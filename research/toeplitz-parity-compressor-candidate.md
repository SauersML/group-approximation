---
rg: 2
id: toeplitz-parity-compressor-candidate
kind: claim
title: The Toeplitz head-tail embedding realizes the parity-headed exact-collapse group
distinct_from:
  schur-child-crosses-toeplitz-compressor: that places a full predicate packet across the Toeplitz boundary; this uses only one external parity bit and one finite-head involution.
---

Let

```text
T=F_2<x,y | yx=1>,       Gamma=EL_4(T),
Lambda=Gamma x C_2.
```

There is an explicit injective endomorphism `alpha:Lambda->Lambda` and a
nonzero character `chi:Lambda->C_2` with `chi alpha=0`.  Therefore the group
`H_T=H(alpha,chi)` of
`parity-headed-compressor-kills-mark-in-exact-matrix-models` is a concrete
finitely generated recursively presented group with a nontrivial central
involution `J` killed by every exact finite-dimensional representation.

Moreover `Lambda` has property `(T)`.  Thus the normalized-HS endpoint for
this candidate is a finite-spectrum, property-`(T)` commutant-return problem,
not a general nonlinear predicate-compilation problem.

No finite presentation of `H_T` and no nonhyperlinearity conclusion is
asserted here.  If `H_T` is proved nonhyperlinear, subgroup closure of
hyperlinearity plus Higman's embedding theorem immediately yields a finitely
presented nonhyperlinear overgroup.
