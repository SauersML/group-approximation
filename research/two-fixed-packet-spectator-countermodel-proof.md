---
rg: 2
id: two-fixed-packet-spectator-countermodel-proof
kind: route
title: Amplify both packet actions and place the Gram projection in the common spectator
target: two-fixed-packet-reynolds-actions-leave-a-gram-spectator
requires: []
artifacts:
  - research/artifacts/fanizza-two-packet-reynolds-localization-firewall-2026-08-21.md
---

Represent the two fixed packet algebras as `A_0 tensor I_N` and
`B_0 tensor I_N`.  Every packet word acts trivially on the last tensor
factor.  Hence `I_V tensor Q_N` commutes with every such word and is fixed by
every associated Reynolds average.  Taking projections `Q_N` of arbitrary
rank proves both the trace flexibility and failure of algebra-factor
localization.

If the fixed joint label algebra is already `End(V)`, its commutant is
exactly `I_V tensor M_N`, so the countermodel is sharp.  Finally, bounded
simple degrees in a fixed finite-dimensional second algebra imply unbounded
irreducible multiplicity along every growing-dimensional representation,
preventing that algebra from equaling the full multiplicity factor.
