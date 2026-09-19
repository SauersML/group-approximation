---
rg: 2
id: quartic-terminal-ledger-closes-diagonal-code-error
kind: route
title: Use a quartic nested-cut gain before terminal high-gap rounding
target: terminal-diagonal-code-error-without-pinching-displacement
requires:
  - current-terminal-ledger-cannot-remove-boundary
  - aggregate-terminal-even-defect-is-quartic-summable
  - uniform-generated-adjoint-gap-rounds-to-central-code
---

The firewall identifies the additive `D` term which must be replaced.
Apply the aggregate quartic ledger to obtain signed terminal balanced energy
`o(lambda_0)` by choosing the cut scale and `lambda_0` diagonally with
`epsilon/lambda_0->0`.  Generated-adjoint rounding on the retained terminal
blocks then has total central-code error `o(1)`, independently of `D`.  This
is `(TDE1)`.
