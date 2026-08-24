---
rg: 2
id: current-terminal-ledger-firewall-proof
kind: route
title: Read the terminal boundary term through generated-adjoint rounding
target: current-terminal-ledger-cannot-remove-boundary
requires:
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
  - uniform-generated-adjoint-gap-rounds-to-central-code
---

Let `D` be the terminal common-pinching displacement.  The established
common-cut ledger charges every bounded-width parity layer and the normalized
complete-pair layer by the original balanced energy plus a dimension-free
constant times `D`; after the terminal sign this remains

```text
E_bal(sign(Phi_F(Q))) <= C (epsilon + D).
```

On a retained terminal block whose generated-adjoint Poincare constant is at
least `lambda_0`, `uniform-generated-adjoint-gap-rounds-to-central-code`
bounds the squared distance to the central code by a constant times the
commutation/parity input with the commutator contribution divided by
`lambda_0`.  Summing the orthogonal terminal blocks therefore gives precisely
an estimate of the form

```text
eta <= C' (epsilon + D) / lambda_0,
```

up to the already controlled parity term.  The stopping schedule uses
`lambda_0 -> 0` and only supplies `epsilon/lambda_0 -> 0`; Pythagoras gives
at best `D <= 1`, not `D=o(lambda_0)`.  Hence this estimate cannot be used to
deduce `D -> 0`: doing so would require the terminal displacement to vanish at
a stronger scale than the conclusion being sought.  The existing ledger is
therefore circular for the terminal-alignment step and a boundary-free or
jointly absorbable replacement is genuinely required.
