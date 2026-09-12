---
rg: 2
id: linton-halo-gives-radical-sofic
kind: route
title: Pass from sofic finite halo pieces to the full Linton radical
target: linton-radical-sofic
requires: [linton-radical-has-equivariant-sofic-halo]
---

Let `K` be a finite subset of `R` and transport it to `L(X)` by `theta^{-1}`.
The halo axiom says

```text
L(X) = < L(Y) : Y is a finite subset of X >.
```

Consequently each element of `theta^{-1}(K)` is a finite product of elements
drawn from finitely many groups `L(Y_i)`.  With `Y` the union of all of those
finite supports, halo monotonicity gives

```text
theta^{-1}(K) is contained in L(Y).
```

The group `L(Y)` is sofic by the prerequisite.  Hence every finite subset of
`R` lies inside a sofic subgroup.  Given a finite multiplication window in
`R`, choose such an `L(Y)` containing the window and take a sofic
approximation there; the same map is a sofic approximation of the original
window.  Thus `R` is sofic.

No action permanence is used in this route.  In particular, it does not infer
the full radical from the already known sofic quotient `R/R'`: it obtains
models of the actual finite subsets of `R` from the hypothesized nonabelian
halo pieces.

