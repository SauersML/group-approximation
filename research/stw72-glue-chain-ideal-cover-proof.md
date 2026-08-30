---
rg: 2
id: stw72-glue-chain-ideal-cover-proof
kind: route
title: Glue chain-ideal cover members through finite sums before taking the directed limit
target: stw72-chain-ideal-cover-wpi-is-purely-infinite
requires:
  - stw72-chain-ideal-wpi-is-purely-infinite
artifacts:
  - research/artifacts/stw72-chain-ideal-cover-collapse-audit-2026-08-30.md
---

Weak pure infiniteness passes to closed ideals.  Thus every `I_lambda` is
weakly purely infinite.  Its own closed ideal lattice is linearly ordered,
so `stw72-chain-ideal-wpi-is-purely-infinite` makes `I_lambda` purely
infinite.

For a nonempty finite subset `F` of `Lambda`, put

```text
D_F = sum_(lambda in F) I_lambda.
```

Finite sums of closed C-star ideals are closed.  We prove by induction on
`|F|` that `D_F` is purely infinite.  The one-member case was just proved.
If `D_F` is purely infinite and `mu` is another index, there is an exact
sequence

```text
0 -> D_F -> D_F+I_mu -> I_mu/(D_F intersect I_mu) -> 0.       (2)
```

The quotient on the right is purely infinite because quotients of purely
infinite C-star algebras are purely infinite.  Kirchberg--Rordam extension
permanence applied to (2) therefore makes `D_(F union {mu})` purely
infinite.  Notice that no assertion about the intersection being purely
infinite is needed.

The finite subsets of `Lambda`, ordered by inclusion, form a directed set,
and the connecting maps `D_F -> D_G` are injective.  Equation (1) identifies
`A` with the C-star inductive limit of this directed system.  Pure
infiniteness is preserved by arbitrary directed C-star inductive limits, so
`A` is purely infinite.  This order of operations is essential: extension
permanence handles each finite sum first, and only then is limit permanence
used.  There is no unproved infinite-extension or limit-ordinal step.

For the topological formulation, ideals correspond to open subsets of
`Prim(A)`, and an open cover has union all of `Prim(A)` exactly when the
closed sum of its corresponding ideals is `A`.
