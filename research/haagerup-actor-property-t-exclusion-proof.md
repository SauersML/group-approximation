---
rg: 2
id: haagerup-actor-property-t-exclusion-proof
kind: route
title: Combine relative Haagerup approximation with Popa rigidity
target: haagerup-actors-cannot-host-property-t-algebraic-envelope
requires: []
---

Popa proves in Proposition 3.1 of *On a class of type II_1 factors with
Betti numbers invariants* that, for any trace-preserving action,

```text
A rtimes Lambda has property H relative to A
    iff Lambda has the Haagerup property.
```

See [Annals of Mathematics 163 (2006), 809--899, Proposition 3.1 and
Theorem 5.4](https://annals.math.princeton.edu/2006/163-3/p03).
Theorem 5.4(2) there says that a finite von Neumann algebra having property H
relative to a type-I subalgebra contains no relatively rigid type-`II_1`
subalgebra.

Here `A` is abelian, hence type I, so the first result applies to
`M=A rtimes Lambda`.  If a property-`(T)` `II_1` factor `P` embedded
trace-preservingly in `M`, then `P subset M` would be relatively rigid.  One
can see this directly: compose any pointwise-identity approximating normal
subunital subtracial completely positive maps on `M` with the
trace-preserving expectation `E_P`; property `(T)` of `P` makes the resulting
maps uniformly close to the identity on the unit ball of `P`, and the usual
Kadison/`L^2` estimate gives the same uniform convergence for the original
maps.  Popa's theorem then forbids `P`.  The argument refers only to the
inclusion `P subset M`, so it also forbids every non-Cartan placement.
