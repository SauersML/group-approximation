---
rg: 2
id: stw72-chain-seeded-quotient-collapse-proof
kind: route
title: Apply the chain seed to the purely-infinite-radical-free quotient
target: stw72-chain-seeded-quotients-wpi-is-purely-infinite
requires:
  - stw72-purely-infinite-radical-reduction
  - stw72-chain-ideal-wpi-is-purely-infinite
artifacts:
  - research/artifacts/stw72-purely-infinite-radical-audit-2026-08-30.md
---

Let `P=P_pi(A)` and `B=A/P`.  By
`stw72-purely-infinite-radical-reduction`, `B` is weakly purely infinite
and has no nonzero purely infinite ideal.

If `B` were nonzero, the quotient-seed hypothesis applied to the particular
quotient `A/P` would give a nonzero ideal `J` of `B` whose closed ideal
lattice is linearly ordered.  Weak pure infiniteness passes from `B` to
`J`.  The established chain-ideal theorem
`stw72-chain-ideal-wpi-is-purely-infinite` would therefore make `J` purely
infinite, contradicting the defining property of `B`.  Hence `B=0`, and the
radical reduction gives that `A=P` is purely infinite.

For the topological wording, the hull-kernel correspondence identifies
`Prim(A/I)` with a closed subspace `F` of `Prim(A)`.  Ideals of `A/I`
correspond to relatively open subsets `U` of `F`, and the ideal lattice of
that ideal is the lattice of relatively open subsets of `U`.  This proves
the equivalence of the algebraic and topological hypotheses.

The advertised inclusions follow directly.  In a scattered space every
nonempty closed subspace has an isolated point, whose singleton is a simple
chain seed.  If `A` is covered by chain ideals and `A/I` is nonzero, the
images of those ideals have dense sum `A/I`, so at least one image is
  nonzero; it is a quotient of a chain-ideal algebra and consequently still
  has a linearly ordered ideal lattice.
