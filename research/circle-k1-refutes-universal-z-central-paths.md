---
rg: 2
id: circle-k1-refutes-universal-z-central-paths
kind: claim
title: A circle K-one class refutes universal controlled central paths for Jiang--Su inclusions
distinct_from:
  stw63-z-inclusions-have-central-path-property: that is the false universal contraction statement; this gives one explicit inclusion and one exactly central unitary which cannot contract.
  stw63-canonical-free-product-copies-are-aue: that is the unresolved approximate-unitary-equivalence test; this counterexample only kills the stronger universal central-path mechanism.
---

Let

```text
B=Z tensor_min C(S^1),
phi:Z->B,                 phi(z)=z tensor 1,
u=1_Z tensor zeta,
```

where `zeta(lambda)=lambda` is the coordinate unitary on the circle.  Then

```text
[u,phi(z)]=0              for every z in Z,
```

but there is no norm-continuous path in `U(B)` from `u` to `1_B`.

Thus the controlled central path property in
`approximate-to-asymptotic-via-central-paths` fails for the unital embedding
`phi`.  In particular, exact centrality alone cannot remove the connected-
component obstruction in an arbitrary codomain.
