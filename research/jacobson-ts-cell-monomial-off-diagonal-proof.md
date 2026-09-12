---
rg: 2
id: jacobson-ts-cell-monomial-off-diagonal-proof
kind: route
title: Extract an impossible basis-support identity from the TS commutator cell
target: jacobson-ts-cell-excludes-monomial-natural-head-models
requires:
  - jacobson-ts-cell-is-independent-after-first-raw-commutation
artifacts:
  - research/artifacts/jacobson-ts-cell-monomial-model-obstruction-2026-09-08.md
---

Use the explicit packet and TS word of the prerequisite. Head root
products give coordinate projections, so tail commutation preserves
all three head coordinate blocks, while `K` centralization preserves
head coordinates one and three and their complementary block `L`.

Set `Z=z_Q-I`, `J=H Z H`, `A=HcH`, `B=Hz_PH`, and
`u=[A,k_P]`. Since `A` centralizes `K`, the head factor of `k`
drops out of `[A,k]`. In the semidirect product of off-diagonal maps
with block diagonal operators, `W=1` implies

```text
[u,B]=z_P,
u.J-z_P.J=Z.
```

On each head-three basis vector, the left side is the difference of
two nonzero scaled basis vectors and the right side is its head-two
basis vector. Hence both left targets must lie in head-two, forcing
`H` to preserve that coordinate block. It already preserves head-one
and head-three. Then `Hb` interchanges head-two and head-three, so
its cube cannot be the identity. Over `F_2`, the displayed support
identity itself is impossible.

The argument is exact in every algebraic dimension. It depends on the
specified monomial and natural-head hypotheses and does not establish
a norm-matrix obstruction for arbitrary representations.
