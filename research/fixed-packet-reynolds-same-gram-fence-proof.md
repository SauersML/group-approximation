---
rg: 2
id: fixed-packet-reynolds-same-gram-fence-proof
kind: route
title: Put the Gram in the common packet spectator and apply the regular-return firewall
target: fixed-packet-reynolds-cannot-supply-same-gram-certificate
requires:
  - two-fixed-packet-reynolds-actions-leave-a-gram-spectator
  - functorial-packet-return-firewall
---

Amplify every fixed packet on `V tensor C^N`.  Its full fixed algebra contains
`I_V tensor M_N`, so the same packet data admit Gram projections of arbitrary
normalized rank, including zero.  Hence those data cannot imply a positive
mass floor.  If a fixed tracially functorial packet operation is added to
charge the missing rank by a proper return, evaluate it in the regular finite
factor; cyclicity contradicts the positive faithful marked trace.
