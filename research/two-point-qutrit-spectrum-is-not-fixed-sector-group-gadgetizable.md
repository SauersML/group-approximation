---
rg: 2
id: two-point-qutrit-spectrum-is-not-fixed-sector-group-gadgetizable
kind: claim
title: A two-point qutrit spectrum is not enforceable by an ordinary-group gadget in one fixed phase sector
artifacts:
  - research/two-point-qutrit-tensor-closure-no-go-proof.md
distinct_from:
  qutrit-psync3-tensor-closure-obstruction: that tensors four admissible pairs to refute equality of two fixed-space projections; this tensors four unary profiles and refutes exclusion of one eigenvalue.
  finite-phase-scalar-groupification-iff-coset-subgroup: that classifies all scalar profile sets abstractly; this is the explicit one-interface tensor obstruction arising from the global-clock positive-ONE3 dualization.
  commuting-finite-phase-gadgets-have-affine-scalar-shadows: that assumes commuting finite-phase auxiliary syntax; this allows arbitrary noncommuting auxiliaries and uses tensor closure of all ordinary group representations.
---

**ESTABLISHED NO-GO.**  There is no finite ordinary-group gadget with a
central order-three element `J`, an order-three interface element `u`, and
any finite collection of auxiliary generators and relators satisfying both:

1. **two-point scalar completeness:** the scalar interfaces `u=1` and
   `u=omega` each extend, after any fixed amplification, to exact
   finite-dimensional representations with `J=omega I`;
2. **unary spectral soundness:** every exact representation with
   `J=omega I` satisfies

   ```text
   Pi_(omega^2)(u)=0.                                  (TQS1)
   ```

Indeed, tensor two exact extensions of `u=omega` and two exact extensions of
`u=1`.  The tensor product is again an exact representation of every
ordinary group relator, its central character is `omega^4=omega`, but its
interface is `u=omega^2`.  This contradicts `(TQS1)`.

Consequently the global-clock reduction
`positive-one3-global-clock-is-z3-lcs-plus-unary-sector` cannot be completed
by an exact local group gadget which accepts the two honest Boolean scalar
values and rejects the third qutrit value.  Noncommuting auxiliaries, finite
packets, more relators, and fixed matrix amplification do not affect the
argument.  Any surviving use of the reduction must change the carrier
architecture, weaken exact scalar completeness, or authenticate `(GQ3)` by
a non-tensor-closed global trace/rank mechanism.

DERIVATION
two-point-qutrit-tensor-closure-no-go-proof
