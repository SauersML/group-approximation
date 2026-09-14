---
rg: 2
id: lpc1-from-shifted-kitaev-reduction
kind: route
title: Shift the standard QMA-complete reduction to obtain combinatorial gap one at constant locality
target: locality-preserving-constant-combinatorial-gap
requires: [kitaev-local-hamiltonian-is-qma-complete, positive-shift-trivializes-exact-combinatorial-soundness]
artifacts:
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
---

## Why sufficient

Apply (PS0) with a fixed rational `epsilon` to the 2-local reduction of
`kitaev-local-hamiltonian-is-qma-complete`. The output is a polynomial-time
reduction from a QMA verifier. It produces 2-local qubit Hamiltonians with
`0<=h'_a<=I`, polynomially many terms and polynomial-bit entries (PS1). By
(PS2), every instance, NO instances included, satisfies (LPC1) with
`beta=1`. Constant locality and constant local dimension hold simultaneously,
so the statement of `locality-preserving-constant-combinatorial-gap` holds as
written.

## What this does not concede

This is not progress toward quantum PCP, and it says nothing about the
Bafna--Nguyen--Zhang amplifier. The same reduction has an inverse-polynomial
YES margin, as recorded in
`anchored-criterion-components-are-shift-satisfiable`. It shows that (LPC1),
read without completeness data, cannot be the content-bearing requirement of
the attack.
