---
rg: 2
id: intrinsic-finite-green-tangent-proof
kind: route
title: Trivialize the square commutator word and exponentiate its CP-Green average
target: intrinsic-finite-green-commutator-step-has-the-correct-tangent
requires:
  - tangent-commutator-covariance-bypasses-code-riesz-endpoint
  - code-laplacian-has-uniform-cp-green-approximants
  - dense-complete-pair-remainders-are-cb-quadratic
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
---

For reflections,

```text
 beta_ij=-(1/2)Q_iQ_j[Q_i,Q_j],
```

so differentiation at a commuting tuple kills the derivative of the
prefactor and gives `(IFG5)`.  The covariance theorem identifies the
normalized average of these derivatives with the coordinate divergence.
The CP Green identity then gives `(IFG6)` after quotienting simultaneous
conjugation.

The skew part in `(IFG3)` is the Lie algebra tangent to the unitary group,
so `(IFG4)` preserves selfadjoint involutions.  If the Green output is the
tangent coordinate `a_i=S_ih_i`, then `a_i` is skew-adjoint and
`[a_i/2,S_i]=-h_i`; hence the sign and factor in `(IFG3)` implement the
negative Newton correction.

For fixed `K`, `G_(Q,K)` is a finite sum of compositions of ucp maps.
Differentiate or use the Duhamel integral for the exponentials in `(IFG4)`.
Every term beyond the derivative contains at least two correction/odd
factors.  The normalized complete-pair double average is bounded by
`dense-complete-pair-remainders-are-cb-quadratic`; constants grow with `K`
but not with `L` or dimension.  The contraction forcing and final sign are
handled by `(TCB7)` and the common-cut ledger.  Sparse words instead see
different `k_i` at their positions and can have uncancelled first-order
terms, which are exactly the two residual items in the claim.
