---
rg: 2
id: free-spherical-bernoulli-projection-proof
kind: route
title: Compute all joint moments of the arithmetic coset Bernoulli projection orbit
target: full-arithmetic-bernoulli-projection-orbit-is-free-spherical
requires: []
---

The coordinate projection `P_(gC)` depends only on the Bernoulli bit at
`gC`.  Repeated occurrences of the same projection do not change a product,
while projections at distinct coordinates are independent.  If `k`
distinct coordinates occur, their simultaneous value is `1` with
probability `2^(-k)`.  This proves `(FBP1)`.

For `Z_g=2P_(gC)-I`, each `Z_g` is an independent mean-zero sign.  Therefore
`tau(Z_g Z_l)` is one if the two cosets agree and zero otherwise, proving
`(FBP2)`.  Covariance under the crossed-product actor is literal:

```text
u_a P_(gC) u_a^*=P_(agC).
```

The coefficient at the base centered sign is consequently
`<Z_C,Ad(u_a)Z_C>=1_C(a)`, proving `(FBP3)` and all positive-definite/Hecke
constraints automatically.

For the SL3 denominator `h`, one has `hC!=C`, so `P` and `Q=P_(hC)` are
independent.  Hence `tau(PQ)=1/4`.  Substitution into the exact balanced-
projection identities of
`sl3-projective-transfer-is-balanced-projection-endpoint-transfer` gives
`D=O=1/2` and projective energy one.

Finally the group unitaries in a crossed product form an exact
representation of `A`.  Thus every relation among the named arithmetic
elementary matrices and `h` holds before the projection moments are
evaluated.  Any implication using only those exact relations, the tracial
axioms and positivity would be valid in `N`, contradicting the displayed
free spherical packet.  Finite-dimensionality or Connes embeddability is
therefore an indispensable additional premise.

