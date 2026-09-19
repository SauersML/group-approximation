---
rg: 2
id: boolean-towers-of-simple-mf-black-holes-proof
kind: route
title: Isolate simple coordinates by commutators and apply the restricted-sum radical formula
target: boolean-towers-of-simple-mf-black-holes
requires:
  - hilbert-hotel-model-full-mf-radical
  - binary-leavitt-elementary-group-is-simple
  - mf-radical-product-and-restricted-sum-formulas
  - hilbert-hotel-mf-indistinguishable-thickenings
---

The restricted-sum formula and `Rad_MF(H)=H` give
`Rad_MF(K_I)=K_I`.  Let `N normal K_I` and suppose an element `x in N` has a
nonidentity `i`th coordinate.  Since the nonabelian simple group `H` is
centerless, choose `y` supported in coordinate `i` with `[x_i,y_i]!=1`.
Then `[x,y]` is a nonidentity element of `N intersection H_i`.  This
intersection is normal in `H_i`, so simplicity gives `H_i<=N`.

Applying this to every coordinate appearing in every element of `N` proves

```text
N=directSum_(i in S)H_i
```

for a unique subset `S`.  Normal subgroups and quotients are therefore
restricted sums of copies of `H`, so the radical formula applies to all of
them.  This proves the Boolean lattice statement.

For finite `I`, the coordinate factors are exactly the minimal nontrivial
normal subgroups.  Their number is an isomorphism invariant.  Finite products
preserve finite generation, property `(T)`, ICC, and perfectness, proving the
finite hierarchy assertions.

For MF `Q`, the product radical formula gives `(BT1)`, and the universal
factorization gives the natural Hom-bijection.  Since the radical is fully
characteristic, an isomorphism between two thickenings would restrict to an
isomorphism between `H^n` and `H^m`, forcing `n=m`.  For `I=N`, the Boolean
normal lattice has cardinality continuum.
