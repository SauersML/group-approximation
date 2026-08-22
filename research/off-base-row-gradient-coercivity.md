---
rg: 2
id: off-base-row-gradient-coercivity
kind: claim
title: The diffuse balanced residual is coercive under its normalized adjoint-gradient step
distinct_from:
  damped-adjoint-step-bypasses-code-riesz-at-exact-base: that proves contraction only for the Jacobian frozen at an exact code tuple; this asks for the intrinsic off-base estimate needed for basin capture.
  balanced-overlay-diffuse-square-function-newton: that permits Newton or alternating projection and previously requested a cb Riesz inverse; this is the narrower first-order descent statement after that inverse is bypassed.
---

OPEN.  Let `F(X)` collect the normalized involution, equality, balanced
parity, and complete-pair residuals for a selfadjoint contraction tuple, and
let `D_X` be its algebraic derivative.  On the retained aggregate-cut block,
prove constants `eta,c,C>0`, independent of length and matrix dimension,
such that

```text
 E(X-eta D_X^*F(X))
   <=(1-c)E(X)+C E(X)^(3/2)+C epsilon_inv,              (ORG1)
```

after quotienting the simultaneous-conjugation gauge.  Here `E` is the
balanced squared residual energy and `epsilon_inv` is the positive
involution forcing floor created by block compression.

The exact-base linear term is established by
`damped-adjoint-step-bypasses-code-riesz-at-exact-base`; the dense quadratic
remainder is established by
`dense-complete-pair-remainders-are-cb-quadratic`.  What remains is to prove
the same descent algebraically before a joint character decomposition is
known, while alternating the bounded local parity/equality corrections so
that their sparse terms do not leave the common row-column basin.

This formulation neither asks for an endpoint cb code-Riesz transform nor
tries to charge physical cut boundary.  The latter contains exact
simultaneous-conjugation motion and is correctly removed by the gauge.

## Attempts

The direct Taylor expansion at an unknown tuple does not inherit `(DAS1)`:
the proof of that gap uses the joint character blocks of an exact code
representation.  Freezing the Jacobian at a hypothetical nearby exact
tuple is circular, since finding that tuple is the basin-capture theorem.
The live attack is instead an SOS expansion of
`<F(X),D_XD_X^*F(X)>` using the complete-pair average, with the bounded
parity faces re-exactified between gradient steps.  The dense quadratic
part already has the required row-column bound; the sparse re-exactification
term is the unproved part of `(ORG1)`.
