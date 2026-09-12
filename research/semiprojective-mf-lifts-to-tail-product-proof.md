---
rg: 2
id: semiprojective-mf-lifts-to-tail-product-proof
kind: route
title: Lift the matrix-corona embedding before the c0 ideal is complete
target: semiprojective-mf-algebras-are-rfd
requires: []
---

Choose an MF embedding

```text
theta:A -> product_n M_(k(n)) / direct-sum_n M_(k(n)).
```

Put `B=product_n M_(k(n))`, let `J=direct-sum_n M_(k(n))`, and let `J_N`
be the ideal of sequences supported on the first `N` coordinates.  Then
`J` is the norm closure of the increasing union of the `J_N`.  By
semiprojectivity, `theta` lifts at some finite stage to a homomorphism

```text
Theta:A -> B/J_N ~= product_(n>N) M_(k(n)).
```

The composition of `Theta` with the quotient by the tail `c_0` ideal is
`theta`.  Since `theta` is injective, `Theta` is injective as well.  Its
coordinate homomorphisms are finite-dimensional representations and separate
the points of `A`.  Thus `A` is RFD.

Quasidiagonality supplies an MF embedding, so the last assertion follows.
No exactness, UCT, or perturbation of c.p. maps is used in this lifting step.
