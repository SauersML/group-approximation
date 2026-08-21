---
rg: 2
id: cyclic-subspace-mean-ergodic-proves-no-excess-fixed-component
kind: route
title: Project onto invariants inside the reducing canonical cyclic subspace
target: embedded-group-algebra-carriers-have-no-excess-fixed-component
requires: []
---

The isometry induced by `pi` embeds `L^2(L(G))` as a closed subspace of
`L^2(M)` invariant under every `Ad pi(h)`. The closed cyclic subspace generated
by the orbit

```text
{Ad pi(h) pi(x):h in H}
```

therefore lies inside the canonical subspace and is reducing for the
conjugation representation.

For any unitary group representation, the orthogonal projection of a vector
onto the invariant subspace belongs to the closed convex hull of its orbit:
it is the unique minimum-norm point of that convex hull. Hence the ambient
fixed projection of `pi(x)` stays in the canonical cyclic subspace and equals
the fixed projection computed there. The latter is precisely the image under
`pi` of `E_(L(H)' cap L(G))(x)`, proving `(EGC1)`.
