---
rg: 2
id: residually-permutational-lamp-extensions-proof
kind: route
title: Push a strict pair along a separating equivariant lamp map into a permutational wreath product with residually finite lamps
target: residually-permutational-lamp-extensions-are-surjunctive
requires:
  - strict-pairs-transfer-to-table-realizations
  - rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive
artifacts:
  - research/artifacts/kun-thom-lamp-quotient-hosts-2026-09-12.md
---

Take a strict pair over `E = V x| Q` with its finite set `F`. Finitely many separating maps
`phi_i : V -> direct_sum_(Y_i) A_i` separate the lamp differences of the window points that
carry different symbols. Their sum into `direct_sum_(disjoint union Y_i) prod A_i` is
`Q`-equivariant, so `(v, g) -> (phi(v), g)` is a homomorphism into a permutational wreath
product with residually finite lamps over `Q`. It respects every product of `F` and separates
the window pairs. The transfer theorem gives a strict pair there, which contradicts the rf-lamp
wreath theorem. Theorem B of the artifact, with Lemmas 3.1--3.2 for the binary form.
