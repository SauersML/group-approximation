---
rg: 2
id: hnn-transports-forbidden-radical-atom-types
kind: claim
title: An HNN edge transports every raw forbidden-radical atom type
distinct_from:
  hnn-selector-chart-transport-preserves-mark-and-types: that transports an elementary-abelian selector chart; this includes the two raw radical words whose four signs label the forbidden small-spin simples.
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out asking conjugacy to create multiplicity; this transports already-created radical types and makes no branching claim.
---

For a forbidden atom `a` in the raw-radical packet, put

```text
E_a=<J,z_1,...,z_k,P_a,Q_a>.                           (HRA1)
```

This is a fixed finite class-two subgroup. On selector atom `a` in the marked
`J=-1` sector, `P_a,Q_a` lie in the packet radical, so the four joint sign
characters of `(P_a,Q_a)` are exactly the four simple types in `(BRD7)`.

Let two packet charts contain isomorphic copies `E_a,E'_a`, with an
isomorphism preserving `J`, carrying selector atom `a` to a chosen target
atom, and carrying `P_a,Q_a` to the two target branch words. Adjoining an HNN
stable letter for this isomorphism has the following properties:

1. the marked base embeds, so every nonidentity marked base word survives;
2. exact finite-dimensional representations have identical complete
   `E_a`-type vectors on the two charts; in particular all four forbidden-atom
   branch multiplicities are transported separately; and
3. after fixed-table exactification of an approximate representation, their
   normalized weighted `L1` discrepancy is at most `C sqrt(E)`.

No nonlinear selector-controlled operator is used: each atom has its own fixed
pair of raw words. The theorem only transports the four branches. It does not
merge them into repeated copies of one next baseline packet; that is the
Morita-reset problem.
