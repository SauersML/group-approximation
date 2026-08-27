---
rg: 2
id: finite-root-windows-share-one-reducing-corona-carrier
kind: claim
title: All finite Heisenberg windows live on one reducing sparse corona carrier
distinct_from:
  finite-root-heisenberg-multiplicity-germs: that constructs intrinsic multiplicity rank germs for each finite window in the ambient corona; this places every window and every branch actor in one nonzero reducing corner selected by the surviving central character.
  torsion-active-core-is-a-uniform-morita-generator: that embeds packet projections into a bounded amplification of a positive-density active corner; this uses a possibly sparse projection but requires no amplification and makes it literally reducing for the self-copy subsystem.
artifacts:
  - research/finite-root-common-corona-carrier-proof.md
---

Let `rho:E_n(R)->U(Q_d)` be a norm-corona representation, and suppose a
finite-order element in the common central root of the binary-Leavitt
Heisenberg self-copy subsystem survives.  Then there are a nonzero projection
`P in Q_d` and a nontrivial additive central character `lambda` such that:

1. `P` reduces every root unitary in the countable Heisenberg subsystem and
   both Morita branch actors;
2. the common central root acts on `P` by `lambda`;
3. every finite additive/multiplicative Heisenberg window compresses to an
   exact unital finite-group representation in the single corner `P Q_d P`;
4. all irreducible multiplicity projections and their restriction maps may
   be taken in that same corner, and retain the exact rank-germ branching
   identities of `finite-root-heisenberg-multiplicity-germs`.

The carrier may have zero normalized rank density, but it is a nonzero
finitely generated projective `Q_d`-module.  Corona projective cancellation
therefore applies to it without any density lower bound.

This theorem aligns the carriers, not the coefficient arrows.  The finite
window representations can still absorb each refinement in new tensor
coordinates inside `P Q_d P`; compatibility of their multiplicity
projections does not yet give a unital ring map

```text
R -> End_(Q_d)(P Q_d).
```

