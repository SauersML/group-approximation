---
rg: 2
id: uncoupled-spectator-cannot-create-first-chord-proof
kind: route
title: Compute the tensor-product relative commutant and its conditional trace
target: uncoupled-spectator-cannot-create-first-chord
requires: []
---

The algebraic commutant of `M_D(C) tensor 1` in
`M_D(C) tensor C[H]` is `I_D tensor C[H]`.  By `(USC1)`, commuting with
`A_0` and `A_1` is the same as commuting with all of `M_D(C)`.  This proves
`(USC3)`.

Put `p_H=(1+z)/2`.  The canonical trace on `(USC2)` is the tensor product of
normalized matrix trace and the canonical group trace of `H`.  Therefore

```text
tau(e p)=tr_D(e) tau_H(p_H),
tau(e)=tr_D(e),                                          (USP1)
```

which proves `(USC4)`.

For the transport obstruction, `(IEC2)` partitions
`e_(i,s)(1+X_i)/2` and `e_(i,s)p` into corresponding algebraic projections,
while `(IEC3)` conjugates each source piece to its target piece by a group
element.  The canonical group trace is invariant under group conjugation;
additivity over the orthogonal partitions gives

```text
tau(e_(i,s)(1+X_i)/2)=tau(e_(i,s)p).                    (USP2)
```

Divide by `tau(e_(i,s))` and apply `(USC4)`.  Every conditional fraction in
`(USC5)` must equal the single number `tau_H(p_H)`.  Hence any nonuniform
table rules out every uncoupled spectator extension and leaves precisely the
coupled projection-and-transport equation `(USC6)`.
