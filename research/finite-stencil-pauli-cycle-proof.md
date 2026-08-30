---
rg: 2
id: finite-stencil-pauli-cycle-proof
kind: route
title: Put the tested Pauli offsets on distinct sites of one finite cycle
target: finite-stencil-pauli-tape-has-marked-periodizations
requires: []
artifacts:
  - research/artifacts/finite-stencil-pauli-cycle-proof.md
---

Choose `m>max_(r in D)|r|`.  On `H=(C^2)^(tensor m)`, let `p_i` and `q_i`
be Pauli `X` and `Z` on tensor coordinate `i in Z/mZ`, let `J=-I`, and let
`S` cyclically permute the tensor coordinates.  Then

```text
p_i^2=q_i^2=J^2=1,
[p_i,q_i]=J,
[p_i,p_j]=[q_i,q_j]=[p_i,q_j]=1  for i!=j,
S p_i S^(-1)=p_(i+1),
S q_i S^(-1)=q_(i+1).
```

Send `t` to `S`, `p` to `p_0`, `q` to `q_0`, and the central sign to `J`.
For every nonzero `r in D`, the inequality `|r|<m` makes `r mod m` different
from zero.  Hence `t^r b t^(-r)` acts at site `r`, disjoint from the site of
`a`, and all four demanded off-site commutators vanish.  The remaining
presentation relations are the displayed same-site Pauli identities.

This is an exact unitary representation of the finite-stencil presentation,
and its sign is maximally nontrivial:

```text
||J-I||_(2,tr) = ||-2I||_(2,tr) = 2.
```

Equivalently, its finite image lies in the semidirect product of the central
product of `m` one-qubit Pauli groups by the cyclic shift.  Thus every finite
stencil has an exact marked periodization.
