---
rg: 2
id: fixed-finite-quotient-adjoint-walls-are-canonical-trace-null
kind: claim
title: Every fixed finite-quotient adjoint sector has zero density in canonical microstates
invalidates:
  - schur-wall-via-polynomial-finite-quotient-route
distinct_from:
  commutant-density-trace-blind: that computes vanishing absolute commutant density in regular-character limits; this treats any adjoint sector on which an infinite quotient kernel acts trivially and gives the finite-window one-over-L bound.
  polynomial-compressor-has-explicit-finite-quotient-wall: that correctly exhibits a positive wall inside one finite quotient representation; this proves that wall cannot occur with positive density in canonical delta microstates of the infinite source group.
  packet-kazhdan-commutant-placement-decouples: that gives a tensor-product countermodel for an unrelated packet; this is a canonical-trace obstruction to using any fixed finite quotient as the positive-density coefficient module.
---

Let `Gamma` be a group and `q:Gamma->Q` a finite quotient with infinite
kernel.  Let `phi_n` be finite-dimensional unitary microstates converging to
the canonical delta trace of `Gamma`.  Suppose `W_n<=M_(d_n)(C)` is an
adjoint subspace on which the quotient kernel acts asymptotically trivially:
for every fixed `k in ker(q)`,

```text
||(Ad(phi_n(k))-I)|_(W_n)||_(HS,ad)=o(d_n).             (FQW1)
```

Then

```text
dim(W_n)/d_n^2 ->0.                                    (FQW2)
```

More quantitatively, choose any `L` distinct elements
`k_1,...,k_L in ker(q)`.  If the adjoint actions fix `W_n` exactly, then

```text
dim(W_n)/d_n^2
 <= (1/L^2) sum_(i,j)|tr_(d_n)(phi_n(k_i)^*phi_n(k_j))|^2
 =1/L+o(1).                                            (FQW3)
```

The same conclusion holds under `(FQW1)` by the triangle inequality.  Since
`L` is arbitrary, `(FQW2)` follows.

Consequently the positive wall in
`polynomial-compressor-has-explicit-finite-quotient-wall` is a valid exact
representation-theoretic witness but not a positive-density canonical-profile
substrate.  Tensor-amplifying that quotient representation does not repair
the problem: the entire amplified quotient adjoint sector is still fixed by
the infinite kernel and is detected by `(FQW3)`.

This does not rule out the polynomial property-`(T)` compressor itself.  It
rules out only a soundness proof whose wall is a fixed finite-quotient module.
A live coefficient wall must retain nontrivial action of arbitrarily large
finite subsets of the quotient kernel, or recur inside the residual kernel
commutant rather than factor through `Q`.
