---
rg: 2
id: hnn-full-child-chart-transports-every-type-corner
kind: claim
title: An HNN isomorphism of full child charts transports every central type corner
distinct_from:
  hnn-selector-chart-transport-preserves-mark-and-types: That transports an elementary-abelian selector chart after reset; this transports the entire finite child group and hence every primitive central type projection.
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: That forbids conjugating the full packet to its multiplicity-doubled child; this conjugates one child chart to an isomorphic next child chart after the doubling has already occurred.
---

**ESTABLISHED.**  Let `C_0,C_1` be isomorphic finite groups and form

```text
Gamma=<G,t | tct^(-1)=theta(c), c in C_0>
```

for an isomorphism `theta:C_0->C_1`.  For every central idempotent `e` of
`C[C_0]`,

```text
t e t^(-1)=theta(e).                                    (HFC1)
```

In particular every primitive central child-type projection, every sum of
such types, and every selector-character cut is transported exactly.  If
both charts are padded by the same finite elementary-abelian pulse-prefix
group, the HNN edge transports each joint child-type/prefix-character corner
as well.

The base embeds by Britton normal form.  For approximate normalized-HS
representations, exactify the two fixed finite charts and average the
intertwiner over `C_0`; polar correction gives `(HFC1)` with
`C sqrt(E)` loss independent of matrix dimension.  External multiplicity
unitaries do not change the conclusion because central type projections are
intrinsic to the finite group algebra.

