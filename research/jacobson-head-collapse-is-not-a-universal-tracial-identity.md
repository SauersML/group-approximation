---
rg: 2
id: jacobson-head-collapse-is-not-a-universal-tracial-identity
kind: claim
title: Jacobson head collapse cannot be a universal tracial identity
artifacts:
  - research/left-regular-representation-defeats-tracial-sos-proof.md
distinct_from:
  jacobson-property-t-and-finite-k-do-not-exactify-the-head: that explains why known rigidity inputs do not imply a matrix ultraproduct modulus; this rules out every argument that would hold in all finite tracial von Neumann algebras.
  jacobson-head-evades-determinant-and-fixed-exterior-power: that audits three concrete invariant families; this gives a structural no-go for universal tracial inequalities.
  bounded-dimension-jacobson-head-has-algebraic-collapse: that proves a matrix statement with dimension-dependent constants; this explains why those constants cannot be replaced by a proof valid in arbitrary finite tracial algebras.
---

**ESTABLISHED FIREWALL.** Put

```text
G=EL_28(F_2<S,T | TS=1>),          w=x_13(1-ST).
```

Fix any finite presentation `<X | R>` of `G`, and let
`lambda:G->U(L(G))` be the left regular representation in the group
von Neumann algebra with its canonical trace. Then every relator is
satisfied exactly, while

```text
||lambda(w)-1||_2^2=2.                                  (JUT1)
```

Consequently there is no modulus `omega(t)->0` for which

```text
||w(U)-1||_2
 <= omega(max_(r in R) ||r(U)-1||_2)                    (JUT2)
```

holds for tuples in **all** finite tracial von Neumann algebras.

In particular, the missing normalized-Hilbert--Schmidt head collapse
cannot follow from a universal tracial sum-of-squares certificate,
generic commutator trace identities, the Fuglede--Kadison determinant,
or any other argument whose hypotheses and conclusion are valid in
every finite tracial von Neumann algebra. Plugging the exact left
regular tuple into such an argument would give `sqrt(2)<=0`.

This does not refute a matrix-only modulus. Rather, it identifies its
necessary content: a successful proof must separate the canonical
trace of `G` from traces factoring through matrix ultraproducts. That
is a Connes-embedding obstruction, not a formal consequence of the
root relations plus tracial positivity. Finite-dimensional rank
integrality or another genuinely matricial mechanism remains possible.

DERIVATION
left-regular-representation-defeats-tracial-sos-proof
