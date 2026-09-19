---
rg: 2
id: entangled-compact-obstruction-proof
kind: route
title: Pull the compact ideal back through the irreducible tensor representation
target: entangled-compact-image-obstructs-tensor-purity
requires: []
---

An irreducible C-star subalgebra of `B(H)` containing one nonzero compact
operator contains all of `K(H)`: cut the given compact by functional calculus
to obtain a nonzero finite-rank operator, and use irreducibility (equivalently,
Kadison transitivity on its finite-dimensional range) to generate all
rank-one operators.  Hence

```text
K(H) subset pi(D).
```

Put `J=ker(pi)` and `L=pi^(-1)(K(H))`.  Since the compact operators form an
ideal in every C-star subalgebra of `B(H)` that contains them, `J` is an ideal
of `L`, `L` is an ideal of `D`, and

```text
L/J isomorphic K(H).
```

Thus `D` has a nonzero elementary ideal-subquotient.

Finally, a pure C-star algebra is nowhere scattered.  Directly at the Cuntz
semigroup level, almost divisibility implies `(2,omega)`-divisibility, hence
the Global Glimm property; an elementary ideal-subquotient violates this at
the rank-one class, since `2y<=1` in `Cu(K(H))` forces `y=0`.  Therefore `D`
cannot be pure.
