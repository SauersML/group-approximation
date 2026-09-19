---
rg: 2
id: termwise-finite-reynolds-holonomy-has-zero-rank-gap-proof
kind: route
title: Conjugation identifies the represented image algebras and their commutants
target: termwise-finite-reynolds-holonomy-has-zero-rank-gap
requires: []
---

The relations `t a t^(-1)=phi(a)` preserve products and inverses, so `phi`
is a homomorphism. Pairing complete tables in both directions makes it an
isomorphism; after applying `rho`, it is still an isomorphism between the two
image groups modulo their respective kernels.

The Reynolds projection is the uniform average of the adjoint action. Change
variables through this image isomorphism:

```text
R_B
 = (1/|rho(B)|) sum_(b in rho(B)) Ad(b)
 = Ad(rho(t)) R_A Ad(rho(t))*.
```

Unitary conjugacy of orthogonal projections preserves rank, proving `(TFH1)`.

