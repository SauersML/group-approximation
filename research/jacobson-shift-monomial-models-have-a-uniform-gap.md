---
rg: 2
id: jacobson-shift-monomial-models-have-a-uniform-gap
kind: claim
title: Recursive Jacobson models have a square-root-two monomial gap and an explicit excluded neighborhood
distinct_from:
  jacobson-ts-cell-excludes-monomial-natural-head-models: that fixes a natural head representation in characteristic two; this treats all complex finite-packet representation types and arbitrary phases in a common basis.
  jacobson-shift-mixed-gap: that asks for a positive gap over all complex matrices; this gives a lower bound conditional on simultaneous proximity to monomial matrices.
artifacts:
  - research/artifacts/jacobson-shift-exact-collapse-and-monomial-gap-2026-09-08.md
---

For admissible data in `jacobson-shift-gap-characterizes-mark-collapse`,
let `delta` be the maximum of its three mixed errors. Let `a` be
the infimum, over common orthonormal bases and arbitrary monomial
unitaries approximating every element of `rho_B(B),rho_C(C)` and
the stable letter `T`, of the maximum operator-norm approximation error.
The approximants need not satisfy any relations. Then

```text
delta+6a>=sqrt(2).
```

In particular simultaneous monomial admissible data have
`delta>=sqrt(2)`, independently of matrix dimension. Any admissible
sequence with `delta->0` must stay at asymptotic distance at least
`sqrt(2)/6` from this class, in the stated finite-packet metric.

Below the square-root-two distance threshold, the approximants' underlying
permutations satisfy the full presentation exactly. Every finite
permutation quotient kills the head. Its monomial approximants are then
diagonal, and the identity `w=[x_12,Q,x_23,Q]` contradicts the norm-two
distance of the retained involution. The constants follow from finite
table errors and the six-letter expression for `W` using grouped
elements of `C` alternating with elements of `B`.

No lower bound for unrestricted `gamma_shift` follows: arbitrary
unitary matrices can lie outside the excluded neighborhood.

DERIVATION
jacobson-shift-permutation-rounding-gap-proof
