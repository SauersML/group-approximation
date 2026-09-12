---
rg: 2
id: nonhyperlinear-from-finite-type-restriction-incidence
kind: route
title: Turn every zero restriction defect into a shared BCS marginal and pull back the canonical corner trace
target: non-hyperlinear-group
requires:
  - finite-type-restriction-incidence-atlas-for-nonce-bcs
  - finite-type-restriction-overlap-defect-formula
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
---

For each context define

```text
V_(c,x)=sum_(a in S_c) a_x p_(c,a)=2P_(c,x,+)-q.
```

Equations `(FTI1)--(FTI2)` make these self-adjoint corner involutions, make
the variables of one context commute, and identify their joint atoms with
`p_(c,a)` for `a in S_c`; all other atoms are zero. By the defect formula
and `(FTI4)`, faithfulness of the canonical trace gives
`P_(c,x,+)=P_(d,x,+)` and hence `V_(c,x)=V_(d,x)` on every overlap.

The context maps therefore assemble to a unital star homomorphism

```text
A(B) -> q C[Gamma]q.
```

The established corner trace-promotion theorem makes the constructed
finitely presented `Gamma` nonhyperlinear, establishing the root.
