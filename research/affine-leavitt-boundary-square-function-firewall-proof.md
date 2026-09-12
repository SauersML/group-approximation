---
rg: 2
id: affine-leavitt-boundary-square-function-firewall-proof
kind: route
title: Substitute the affine-Leavitt left regular representation into every tracial boundary operation
target: affine-leavitt-tracial-square-function-firewall
requires:
  - affine-leavitt-steinberg-mark-is-fd-invisible
---

The required input from
`affine-leavitt-steinberg-mark-is-fd-invisible` is only the independently
proved algebraic fact `w_A!=1`; its exact finite-dimensional collapse is not
used.

Every operation listed in the claim is functorial for a finite tracial von
Neumann algebra.  Finite packet averaging is a trace-preserving conditional
expectation, operator Gram matrices remain positive, spectral calculus and
coarea are available for bounded positive operators, and every quoted
Hilbert-space inequality is valid in `L2(M,tau)`.

Apply the purported derivation with

```text
M=L(Gamma_A),       U_s=lambda(s).
```

All presentation relators evaluate to one.  The canonical trace is exactly
delta at the identity, so every finite separation error is zero.  But

```text
||lambda(w_A)-1||_2^2
 =tau((lambda(w_A)-1)^*(lambda(w_A)-1))
 =2-2 Re tau(lambda(w_A))
 =2.
```

Hence a terminal upper bound with residual `b<2` is impossible.  Since the
argument applies to the entire derivation rather than to a predetermined
spectral cut, allowing existential coarea thresholds or finitely many
nested cuts changes nothing.
