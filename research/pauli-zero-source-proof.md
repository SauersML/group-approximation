---
rg: 2
id: pauli-zero-source-proof
kind: route
title: Apply Schur's lemma on the unique marked Pauli spin type
target: pauli-zero-atom-removes-acceptance-source-deficit
requires: []
---

The `J=-1` representation of `E_m` is uniquely
`C^(2^m) tensor M`, with Pauli action on the first factor.  Hence every
commuting source is `Q=I tensor q`.  For the computational zero atom
`P_0=|0^m><0^m| tensor I`,

```text
||P_0Q||_2^2=2^-m tau(Q).
```

Finite-group exactification and averaging over the fixed Pauli table give
the same identity up to a dimension-independent error controlled by the
named commutator defects.

The fresh-control block encoder satisfies
`P_0W_gameP_0=P_0 tensor T_game`.  If `T_game` has norm at most `rho<1`, then
for `G=P_0Q`,

```text
||G||_2^2-Re tau(QP_0W_gameP_0Q)
 >=(1-rho)2^-m tau(Q)-o(1).
```

Thus no separate source deficit remains.  The exact perfect model extends
by putting the BCS algebra on `M`, where the perfect zero-control Gram vector
is fixed.  Controller orientation and the mixed return upper bound remain
separate interfaces, as stated.
