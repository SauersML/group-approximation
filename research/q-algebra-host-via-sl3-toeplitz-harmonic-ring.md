---
rg: 2
id: q-algebra-host-via-sl3-toeplitz-harmonic-ring
kind: route
title: The SL_3(Z) Toeplitz harmonic ring is a host once its elementary groups are finitely presented for infinitely many ranks
target: q-algebra-with-fp-simple-projective-elementary-group
requires:
  - sl3-toeplitz-harmonic-pe-groups-are-simple
  - sl3-toeplitz-harmonic-elementary-groups-are-fp
artifacts:
  - research/artifacts/gq-referee-b-sl3-toeplitz-harmonic-pe-groups-are-simple.md
  - research/artifacts/gq-referee-c-sl3-toeplitz-harmonic-pe-groups-are-simple.md
---

`R_T` contains `Q` (`sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`, part 1).

For every `N >= 3`, `PE_N(R_T)` is simple, and it is finitely presented exactly when `E_N(R_T)` is
(`sl3-toeplitz-harmonic-pe-groups-are-simple`). By `sl3-toeplitz-harmonic-elementary-groups-are-fp`,
this happens for infinitely many `N`.

So `R_T` witnesses `q-algebra-with-fp-simple-projective-elementary-group`. ∎

Reviewed: `gq-referee-b` and `gq-referee-c` PASS, conditional on parts 1–3 of the ring node.
