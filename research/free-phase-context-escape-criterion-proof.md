---
rg: 2
id: free-phase-context-escape-criterion-proof
kind: route
title: Compare context atoms with the joint spectral fibers of the preserved signs
target: free-phase-context-escape-criterion
requires:
  - one-binary-marginal-block-escape
  - sequential-marginal-holonomy-is-conditional-rank-matching
---

The joint eigenspace for a sign pattern `sigma in {+1,-1}^S` is

```text
Q_sigma=sum_(a:a|_S=sigma) P_a.                           (FEC3)
```

By the block decomposition in
`sequential-marginal-holonomy-is-conditional-rank-matching`, the simultaneous
commutant of the `d_x` is the direct sum of the full matrix algebras on the
ranges of the nonzero `Q_sigma`.  It contains a unitary mixing
two distinct context atoms precisely when some sum `(FEC3)` has at least two
terms.  This is exactly failure of injectivity in `(FEC2)`.

Choose a two-vector Hadamard rotation inside such a `Q_sigma`; the calculation
in `(OBM6)` and the free-word coefficient argument then move the two coarse
assignment projections outside the root block.  If every `(FEC3)` has one
term, each `P_a` is a polynomial in the commuting signs, so every unitary in
their commutant fixes it.
