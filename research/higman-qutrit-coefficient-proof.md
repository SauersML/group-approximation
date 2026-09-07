---
rg: 2
id: higman-qutrit-coefficient-proof
kind: route
title: Evaluate four rational Cayley matrices and compare their HS energies exactly
target: higman-hs-word-coefficient-exceeds-sixteen
requires: []
artifacts:
  - research/artifacts/higman-qutrit-coefficient-bound.md
  - research/artifacts/higman-qutrit-coefficient-witness.json
  - experiments/higman_qutrit_witness.py
  - experiments/hs_word_certificate.py
---

Construct the four skew-Hermitian matrices from the displayed integer
rows and apply the Cayley transform. Skew-Hermitianity proves exact
unitarity. Exact multiplication of the four relators gives
`e_(g_0)>16/7` and `0<sum_j e_(r_j)<1/7`. Thus
`e_(g_0)>16 sum_j e_(r_j)`, contradicting any proposed coefficient at
most sixteen. The artifact supplies the complete matrix definition;
the committed witness and verifier replay every rational operation.

No approximate numerical comparison, bounded search, or existence
conclusion is asserted by this direct finite proof.
