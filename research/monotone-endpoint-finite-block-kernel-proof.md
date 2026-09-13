---
rg: 2
id: monotone-endpoint-finite-block-kernel-proof
kind: route
title: Identify functions on the two-end compactification and check every finite-support invertible block
target: monotone-subshift-endpoint-kernel-is-finitary-simple
requires: []
artifacts:
  - research/artifacts/pestov91-monotone-exact-mf-quotient-2026-09-13.md
---

Sections 1--4 give the full proof. Locally constant functions on the
monotone subshift are sequences eventually constant at each end.
Crossed-product normal forms act faithfully on the transition orbit.
Vanishing endpoint symbols means precisely finite matrix support;
the translates `u^i e u^{-j}` of its singleton projection are all the
matrix units.

A group element in the kernel is an invertible finite block extended
by the identity. Conversely every such block lies in the elementary
group: over `F_2` its determinant is one, and within-colour transvections
are commutators through another colour. Stable finite special linear
groups give simplicity of the kernel. Evaluating Laurent polynomials
at nonzero elements of finite fields separates the quotient, proving
residual finiteness and identifying the finite residual.
