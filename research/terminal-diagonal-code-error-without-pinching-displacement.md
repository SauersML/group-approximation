---
rg: 2
id: terminal-diagonal-code-error-without-pinching-displacement
kind: claim
title: Control terminal diagonal code error without assuming the final pinching displacement
distinct_from:
  common-cut-contraction-sign-has-complete-balanced-energy-ledger: that gives the available estimate with an additive terminal boundary term; this asks for a boundary-free or absorbable replacement
  multicharacter-pvm-alignment-modulo-simultaneous-gauge: that aligns terminal character atoms once their diagonal code error is small; this must justify that prerequisite without already knowing the desired displacement is small
---

OPEN.  Let `D` denote the terminal common pinching displacement `(TCP1)` and
let `eta` denote the weighted error obtained by signing the terminal
contractions and applying generated-adjoint-gap rounding on the terminal
blocks.  Prove either

```text
eta=o(1)                                                 (TDE1)
```

from the original balanced energy `epsilon`, the contraction-tree stopping
rules, and `epsilon/lambda_0->0`, without assuming `D=o(1)`; or prove an
absorbable coupled inequality which, together with multi-character PVM
alignment, forces both `eta` and `D` to vanish.

The current one-cut ledger gives only

```text
E_bal(sign(Phi_F(Q))) <= C(epsilon+D),
eta <= C'(epsilon+D)/lambda_0.                           (TDE2)
```

Since `lambda_0->0`, `(TDE2)` cannot be inserted into an alignment estimate
to prove `D=o(1)`; it assumes the desired conclusion at a stronger scale.
Spike quarantine controls total discarded trace, not the operator norm or
fourth moment of the aggregate off-diagonal part, so it does not remove the
`D` term in `(TDE2)`.

## Attempts

1. **Invoke high-gap rounding leafwise.**  Circular under the existing
   ledger: its input pair/parity energy already contains the unknown final
   displacement.
2. **Use the one-cut quartic common-rotation gain.**  A single smooth
   two-character rotation has quartic contraction residual and quadratic
   boundary, but no current theorem sums that quartic gain over the whole
   nested tree.  Aggregate compression only gives the linear bound in
   `(TDE2)` without an additional delocalization estimate.
3. **Use spike quarantine.**  It makes the union of explicitly detected
   spike supports small.  It does not bound the aggregate off-diagonal
   contraction defect on the retained diffuse tree.
