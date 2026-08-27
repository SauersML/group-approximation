---
rg: 2
id: scaled-kazhdan-transport
kind: claim
title: Kazhdan transport of asymptotic commutants at every scale
distinct_from:
  kazhdan-asymptotic-commutant-transport: That claim is the dimension-normalized transport for operator-norm-bounded commutants; this one quantifies over every nonnegative weight and needs only Frobenius-mass boundedness.
artifacts:
  - GroupApproximation/Sofic/ScaledKazhdanTransport.lean
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
---

For every nonnegative weight sequence `w`, every one-sided compressor of a
Kazhdan image acts in both directions on the `w`-mass-bounded, `w`-scaled
Frobenius asymptotic commutant of every operator-norm almost
representation.  The dimension weight recovers (and strictly strengthens)
the normalized-HS transport theorem; rank weights give the
arbitrary-rescaling matricial Mautner statement on the mass sector.
