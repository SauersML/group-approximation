---
rg: 2
id: hnn-selector-chart-transport-preserves-mark-and-types
kind: claim
title: An HNN edge transports a reset selector chart to the next context without global commutation
distinct_from:
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out using conjugacy to implement a factor-two restriction; this uses conjugacy only after the reset, when source and target selector types have equal dimensions and should be preserved.
  nested-schur-multiplicity-wire-globalizes-selectors: that places the next packet in the old commutant; this keeps the next context merely conjugate to a transverse reset MASA.
---

Let `G` contain two isomorphic elementary-abelian selector subgroups `D_0`
and `D_1`, where `D_0` is the transverse chart output by a branch reset and
`D_1` is the next BCS context. For a fixed isomorphism `theta:D_0->D_1`, form

```text
Gamma=<G,v | v d v^(-1)=theta(d), d in D_0>.                   (HST1)
```

Then:

1. `G` embeds in `Gamma`, so every nonidentity marked base word survives;
2. `D_0` and `D_1` are conjugate rather than jointly centralized, so `(HST1)`
   does not classicalize the two contexts; and
3. in finite-dimensional approximate representations, after fixed-table
   exactification, the normalized weighted `L1` discrepancy of their complete
   character-multiplicity vectors is at most `C sqrt(E)`.

Thus a finite HNN selector edge is a valid post-reset context atlas. It
preserves multiplicity exactly—which is correct at this stage—and is not the
invalid attempt to make conjugacy itself perform the Schur doubling.

