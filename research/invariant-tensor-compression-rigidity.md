---
rg: 2
id: invariant-tensor-compression-rigidity
kind: claim
title: Compression creates no invariant tensors of any type in exact finite dimension
distinct_from:
  commutant-no-growth: That claim is the type (1,1) case, since End(V) is V tensor V-bar with the adjoint action; this one covers every finite tensor type and every functorial construction, so compression also creates no invariant vectors, forms, intertwiners, or multilinear structures.
---

Let `rho` be a finite-dimensional representation of `H` on `V`, let
`s L s^{-1} <= L`, and let `T` be any finite tensor construction — 
`V^{tensor p} tensor Vbar^{tensor q}`, finite direct sums, duals,
Hom-spaces, `Sym^k`, `Wedge^k` — with its induced `H`-action on `T(V)`.
Then the fixed subspaces agree:

```text
T(V)^L  =  T(V)^(s L s^{-1}).
```

So one-sided compression cannot create: invariant vectors, invariant
bilinear or Hermitian forms, intertwiners between tensor constructions,
invariant tensors, invariant algebra structures, or new tensor relations.
Ranging over all types `(p,q)` this is the invariant-tensor shadow of
`zariski-envelope-compression-rigidity` — a Tannakian rigidity statement:
the tensor category data that an exact finite-dimensional representation
attaches to `L` and to `s L s^{-1}` coincide.  `commutant-no-growth` is the
single case `T(V) = V tensor Vbar = End(V)`, and
`GroupApproximation/Criterion/ExactCompression.lean` already contains the
elementary fixed-space engine this instantiates; the general `T` is the
natural API enlargement.  The asymptotic counterpart at fixed type is
`kazhdan-tensor-type-transport`.
