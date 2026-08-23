---
rg: 2
id: single-odd-whitehead-selector-row-no-go-proof
kind: route
title: Conjugate two balanced involutions and compare the induced Pauli outer classes
target: odd-selector-row-balances-or-kills-outer-action
requires:
  - controlled-fine-reflection-superrank-orientation-law
  - balanced-controlled-whitehead-return-checksum
  - shared-gauge-cz-cancellation-needs-an-identity-outer-anchor
---

A noncentral Pauli reflection on the two-qubit spin module has eigenvalue
multiplicities `(2,2)`.  After tensoring with `C^2`, `rho(r)` has
multiplicities `(4,4)`.  Controlled-Z has multiplicities `(3,1)`, so

```text
C tensor diag(1,-1)
```

has positive multiplicity `3+1=4` and negative multiplicity `1+3=4`.
Two self-adjoint involutions are unitarily conjugate exactly when their two
spectral multiplicities agree.  This supplies `W` in `(SOW4)` and proves the
exact countermodel.

For `(SOW5)`, normalized trace is bounded by normalized Hilbert--Schmidt norm:

```text
|tr(rho(t))-tr(Wrho(r)W^*)|<=delta_W.
```

The second trace is zero, while

```text
tr(C tensor V)=tr(C)tr(V)=mu/2.
```

Substitution into the controlled superrank orientation law proves
`(SOW5)--(SOW6)`.

Finally, if `W` normalizes `rho(P)`, then `WrW^*` belongs to `rho(P)` and
conjugation by it induces an inner automorphism of `rho(P)`.  Equation
`(SOW2)` identifies this with conjugation by `t`.  On a faithful marked
packet the latter induces the nontrivial controlled-Z class on `P/Z(P)`,
whereas inner automorphisms of the extraspecial group act trivially on the
quotient.  This contradiction proves the normalizer half of the dichotomy.
