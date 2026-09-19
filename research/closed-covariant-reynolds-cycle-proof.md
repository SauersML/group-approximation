---
rg: 2
id: closed-covariant-reynolds-cycle-proof
kind: route
title: Compose the transported character idempotents and commutant ranges
target: closed-covariant-reynolds-cycle-has-full-overlap
requires:
  - finite-edge-reynolds-overlap-follows-character-transport
---

For one edge, `(FEO3)--(FEO4)` give

```text
rho(t_i)e_i rho(t_i)^*=e_(i+1),
T_i R_i T_i^*=R_(i+1).                                 (1)
```

The second equality can also be checked directly: conjugation by `rho(t_i)`
is a unitary on the adjoint Hilbert space, carries operators supported on
`e_i H_rho` onto operators supported on `e_(i+1) H_rho`, and carries the
commutation equations for `rho(H_i)` bijectively onto those for
`rho(H_(i+1))`. Hence it carries the corresponding closed subspace onto the
next one, and therefore conjugates their orthogonal projections.

Iterating `(1)` proves `(CCR3)`. Under `(CCR4)`, the defining supported
commutant subspaces at the two endpoints are literally the same, so
`R_r=R_0`. From `T R_0 T^*=R_0` we also have `T^*R_0T=R_0`, and therefore

```text
R_0 T^*R_0TR_0=R_0.
```

Taking normalized adjoint trace proves `(CCR5)`.

For a packet automorphism `beta`, replace `H_(i+1)` by `beta(H_i)` and
`chi_(i+1)` by its transported character. The same proof applies verbatim.
In particular, evaluating `beta(H_i)` in the renamed target sector is
unitarily equivalent to evaluating `H_i` in the source sector. Calling
`beta` a reset does not change this fact. The only way to compare instead
with an *unmoved* target frame is to add another identification; if that
identification is covariant, it is another edge in the same calculation and
the closed composite still has full overlap.

