---
rg: 2
id: groupify-raw-radical-via-hnn-morita-reset
kind: route
title: Transport raw forbidden atoms by HNN and merge them through one Morita reset
target: groupify-raw-radical-violation-chart
requires:
  - hnn-transports-forbidden-radical-atom-types
  - raw-radical-branch-morita-reset
  - context-local-schur-packet-marked-extension
  - bounded-overlap-syndrome-energy-accounting
---

For each forbidden atom, exactify its finite radical subgroup and use the HNN
edge to transport the complete four-branch type vector. The Morita reset adds
those orthogonal branch multiplicities into one next baseline type at the
common small-spin scale. Fixed-word telescoping transfers the original BCS
atom mass to the exact chart, and bounded-overlap accounting sums the losses.
The marked local-packet extension and the reset's exact completeness preserve
the nonidentity word. These are precisely the four clauses of the target.
