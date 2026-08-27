---
rg: 2
id: cyclic-source-desynchronization-proof
kind: route
title: Build an exact covariant cycle with orthogonal swap sources
target: cyclic-conjugacy-does-not-synchronize-swap-sources
requires: []
---

Let `H=directSum_(v in Z/m)K_v`, let `Q_v` project onto `K_v`, and let `U`
cyclically permute the summands.  Then `UQ_vU^*=Q_(v+1)`.  Regard
`S_v=Q_v` as a partial isometry and form its standard two-by-two swap
reflection `J_(S_v)`.  Exactly,

```text
diag(U,U)J_(S_v)diag(U,U)^*=J_(S_(v+1)).
```

The cycle closes and every local swap relation holds, yet

```text
Q_vQ_w=0 (v!=w),   tau(Q_v)=1/m.
```

Common amplification preserves these identities.  More generally, the
permutation representation of any vertex-transitive graph gives the same
model.  Expansion cannot detect it because labels and carriers covary along
every edge.  Equal trace tests control rank but not coordinate.  This exact
model disproves source synchronization from cyclic conjugacy alone.
