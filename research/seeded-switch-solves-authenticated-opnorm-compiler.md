---
rg: 2
id: seeded-switch-solves-authenticated-opnorm-compiler
kind: route
title: Instantiate the threshold-free compiler with the literal invisible mark
target: authenticated-opnorm-challenge-compiler
requires:
  - literal-central-mark-corona-invisible
  - marked-mf-radical-seed-gives-proof-triggered-compiler
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
---

Use the literal finitely presented group `E` and its mark `w`, which is
nontrivial and belongs to the MF radical. Apply
`marked-mf-radical-seed-gives-proof-triggered-compiler`: adjoin one dummy free
generator and kill it exactly when the input machine halts. The halting group
is `E`, while the nonhalting group is `E*Z`; the same marked word survives in
the first and lies in the MF radical of the second. This supplies the exact
TFM1--TFM2 compiler semantics required by the target.
