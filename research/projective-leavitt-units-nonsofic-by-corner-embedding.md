---
rg: 2
id: projective-leavitt-units-nonsofic-by-corner-embedding
kind: route
title: The scalar quotient contains the nonsofic unit group
target: projective-leavitt-unit-groups-mod-scalars-are-nonsofic
requires: [leavitt-units-embed-in-their-scalar-quotient, d-ary-leavitt-groups-nonsofic-over-finite-fields, sofic-passes-to-subgroups]
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

The corner homomorphism embeds `L_k(1,2)^x` in `L_k(1,2)^x / k^x`. The unit group
is nonsofic for every finite field `k`. A sofic group has only sofic subgroups, so
the quotient is not sofic.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 24 of the verification
artifact). `units_not_isSofic` is stated for every nontrivial countable algebra over a
finite field that carries a binary family. So it applies to `L_(F_3)(1,2)` itself.
