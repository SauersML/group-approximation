---
rg: 2
id: boone-higman-iff-simple-kazhdan-decidable-inputs-proof
kind: route
title: Envelope each decidable input in a decidable simple Kazhdan group, and specialize in the other direction
target: boone-higman-iff-simple-kazhdan-decidable-inputs
requires: [fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree, property-t-implies-property-fa]
---

- **(1) ⇒ (3) ⇒ (2).** A simple FA group with solvable word problem is a
  finitely generated group with solvable word problem, so (1) applies to it. An
  infinite finitely generated simple Kazhdan group has property FA by
  `property-t-implies-property-fa`, so (3) applies to it.
- **(2) ⇒ (1).** Let `G` be finitely generated with solvable word problem. By
  `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`, `G ≤ H` with `H`
  infinite, finitely generated, simple, Kazhdan and with `WP(H) ≤_T WP(G)`
  solvable. By (2), `H ≤ P` with `P` finitely presented simple, so `G ≤ P`. `∎`
