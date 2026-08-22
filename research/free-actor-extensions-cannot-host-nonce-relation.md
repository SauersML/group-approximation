---
rg: 2
id: free-actor-extensions-cannot-host-nonce-relation
kind: claim
title: Free-actor extensions cannot contain the non-CE relation factor
distinct_from:
  abelian-by-virtually-free-groups-are-sofic: that concerns Haar algebraic crossed products and their dual semidirect-product groups; this concerns arbitrary pmp actions and the singular Feldman--Moore quotient which forgets stabilizers.
  coinduced-coordinate-fourier-test-factorizes: that computes the Haar Fourier law of a coinduced label process; this proves that coinduction or any skew extension by the native free actor cannot turn the non-CE relation quotient into a von Neumann inclusion.
---

Let `F` be a countable free group.  For every pmp action
`F curvearrowright (Y,nu)`, including every compact, skew-product, diagonal
free, or coinduced action which still has actor `F`,

```text
L^infinity(Y) rtimes F
```

is Connes embeddable.  Consequently it cannot contain a trace-preserving copy
of the non-Connes-embeddable relation factor obtained from the Manzoor IRS.

More precisely, realize that IRS as the stabilizer distribution of an action
`F curvearrowright (X,mu)` and let `R` be its orbit relation.  The canonical
algebraic map

```text
q_0 : L^infinity(X) rtimes_alg F -> L(R),
q_0(a u_g)=a v_g,
```

which forgets which group element represented an orbit arrow, is onto at the
weak-closure level but does **not** extend to a normal map from the von Neumann
crossed product.  Thus the familiar transformation-groupoid presentation gives
the required non-CE algebra only as a singular quotient, never as the inclusion
needed by the algebraic-envelope compiler.  Passing to a free diagonal
extension does not repair this: its crossed product is still Connes embeddable.

