---
rg: 2
id: context-local-schur-packet-marked-extension-proof
kind: route
title: Decompose each commuting context into characters and use infinite packet multiplicity
target: context-local-schur-packet-marked-extension
requires:
  - predicate-rank-gate-doubles-restriction-multiplicity
---

Fix a context `c` with commuting involutions `z_1,...,z_k`. Their joint
spectral projections decompose

```text
H=directSum_(x in {0,1}^k) H_x.
```

In selector sector `x`, the packet algebra of `B_c` has a simple module
`T_x` of dimension `2^(N_c+f_c(x))`. Choose one infinite Hilbert space `K`
whose dimension is unchanged by multiplication by any of the finitely many
packet dimensions. Every nonzero `H_x tensor K` is then unitarily isomorphic
to

```text
T_x tensor M_x
```

for an infinite multiplicity space `M_x`. Put the `B_c` action
`T_x tensor I_(M_x)` on this summand. Its central selector signs are exactly
the signs of the original `z_i`, so these sectorwise actions assemble into a
representation of `B_c` extending the amplified context observables. Empty
sectors require no choice.

Repeat this construction for every context. The packet generator sets are
disjoint away from the identified input selectors and the common scalar sign,
and no cross-context packet relation is imposed, so their independently
chosen operator families coexist on `H tensor K` even though different BCS
contexts need not commute. Set the common sign to `-I`.

Finally the original BCS words act as `pi(.) tensor I_K`. Hence
`pi(w) tensor I_K!=I`, and adjoining the local packets does not erase the
mark.
