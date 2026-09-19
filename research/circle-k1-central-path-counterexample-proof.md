---
rg: 2
id: circle-k1-central-path-counterexample-proof
kind: route
title: Detect the exactly central circle unitary in K-one
target: circle-k1-refutes-universal-z-central-paths
requires: []
---

The coordinate unitary `u=1_Z tensor zeta` lies in the exact relative
commutant of `phi(Z)=Z tensor 1`, so it satisfies

```text
max_(g in G) ||[u,phi(g)]||=0
```

for every finite `G subset Z` and every positive `delta`.

The Jiang--Su algebra is nuclear, belongs to the UCT class, and has

```text
K_0(Z)=Z[1_Z],            K_1(Z)=0.
```

The Kunneth theorem therefore gives

```text
K_1(Z tensor_min C(S^1))
  = K_0(Z) tensor K_1(C(S^1))
  = Z,
```

and the external product of `[1_Z]` with the circle generator `[zeta]` is its
generator.  Hence `[u]` is nonzero in `K_1(B)`.  A norm-continuous unitary
path from `u` to `1_B` would make `[u]=[1_B]=0` in `K_1(B)`, a contradiction.

To test the central path property, take for instance `F={1_Z}` and
`epsilon=1`.  Whatever finite `G` and `delta>0` the property proposes, the
unitary `u` satisfies the antecedent exactly, while the required path to `1`
does not exist even without the commutator bound.  This disproves the
property for `phi` and hence refutes the universal target.
