---
rg: 2
id: stw72-chain-seeded-quotients-wpi-is-purely-infinite
kind: claim
title: Chain seeds in every nonzero quotient collapse weak pure infiniteness
distinct_from:
  stw72-chain-ideal-cover-wpi-is-purely-infinite: that requires good ideals of the original algebra to cover it; here a chain-ideal seed may appear only after passing to a quotient, and no family of chain ideals in the original algebra is assumed to cover anything.
  stw72-scattered-primitive-spectrum-wpi-is-purely-infinite: an isolated point is a simple chain seed, but the seed here may have an infinite chain ideal lattice and need not contain any simple ideal.
artifacts:
  - research/artifacts/stw72-purely-infinite-radical-audit-2026-08-30.md
---

Let `A` be weakly purely infinite.  Assume that every nonzero quotient `A/I`
contains a nonzero closed ideal whose own closed ideal lattice is linearly
ordered.  Then `A` is purely infinite.

Equivalently, write `X=Prim(A)`.  The hypothesis says that every nonempty
closed subspace `F` of `X` contains a nonempty relatively open subset `U`
whose lattice of relatively open subsets is linearly ordered.  Under this
intrinsic topological condition, weak and plain pure infiniteness coincide.

The theorem needs neither a preassigned composition series nor a cover of
`A` by chain ideals.  It includes the scattered-spectrum theorem (take an
isolated point in every nonempty closed subspace), the global chain theorem,
and the chain-ideal-cover theorem, but also permits the first useful chain
piece to occur only in a proper quotient.  The three-level rational-poset
graph in the audit satisfies the quotient-seed hypothesis while having no
chain-ideal cover, no isolated primitive point, and no nonzero simple ideal.
