---
rg: 2
id: aggregate-terminal-even-defect-is-quartic-summable
kind: claim
title: Aggregate terminal even-word defects gain one small cut-boundary factor
distinct_from:
  common-cut-contraction-sign-has-complete-balanced-energy-ledger: that safely bounds terminal damage linearly by total pinching displacement; this asks for the nonlinear gain from many individually small nested generated-algebra cuts
  one-anchor-grading-makes-parity-damage-quadratic: that gives the exact quadratic gain for one grading; this must sum it through the orthogonal nested cut tree
---

OPEN.  Let `D` be the exact Pythagorean sum of terminal cut boundaries and
let `rho` be a uniform upper scale for every individual retained cut
boundary after spike quarantine.  Prove a dimension-free nested-tree
estimate of the form

```text
E_bal(sign(Phi_F(Q))) <= C(epsilon+rho D),               (ATE1)
```

or any estimate with a coefficient `o(1)` multiplying `D`.  The contraction
tree is produced by spectral cuts in the successively generated compressed
algebras, and exact parity supplies the Loewner spreading inequality at
every node; arbitrary external nested PVMs are not the target.

Since cut Pythagoras gives `D<=1` and the low-gap/coarea schedule can make
`rho->0`, `(ATE1)` would make terminal signed balanced energy `o(1)` without
assuming `D=o(1)`.  Terminal generated-adjoint rounding with
`epsilon/lambda_0->0` would then give the boundary-free diagonal character
error required by
`terminal-diagonal-code-error-without-pinching-displacement`.

## Attempts

1. **Apply the one-cut ledger after forming the final PVM.**  This forgets
   which off-diagonal leaf blocks were created together and gives only the
   linear `O(D)` term.
2. **Sum one-cut quadratic errors before terminal sign.**  Lowest-common-
   ancestor orthogonality controls squared boundaries, but products of
   off-diagonal blocks from different levels need an additional martingale
   orthogonality or parity cancellation to gain `rho`.
3. **Use spike trace alone.**  Small spike carrier controls concentrated
   fourth moments only on quarantined supports.  The diffuse retained tree
   still needs `(ATE1)`.
