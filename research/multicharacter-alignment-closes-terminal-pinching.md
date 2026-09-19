---
rg: 2
id: multicharacter-alignment-closes-terminal-pinching
kind: route
title: Apply simultaneous character alignment to the terminal signed leaves
target: terminal-common-pinching-displacement-vanishes
requires:
  - two-code-character-cut-recenters-to-one-coordinate
  - sequential-character-recentering-has-decision-tree-loss
  - uniform-generated-adjoint-gap-rounds-to-central-code
  - terminal-diagonal-code-error-without-pinching-displacement
  - multicharacter-pvm-alignment-modulo-simultaneous-gauge
---

Run the already established contraction cut tree and spike budget at a scale
`lambda_0` with `epsilon/lambda_0->0`.
`terminal-diagonal-code-error-without-pinching-displacement` supplies the
noncircular input needed to sign and round the terminal diagonal tuple to
central code characters with total error `eta=o(1)`.  Apply the
multi-character alignment theorem simultaneously to all central terminal
atoms.  Its gauge-adjusted PVM has terminal displacement
`omega(epsilon+eta)=o(1)` and preserves or merges only equal character
sectors, so the terminal gap decomposition remains valid.  This is `(TCP1)`.
