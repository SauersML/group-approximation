---
rg: 2
id: hard-tail-soft-anchor-multiscale-centralization
kind: route
title: Dead — hard-repair scalar tails and iterate quadratic random anchoring on the low core
target: multiplicity-space-centralization-after-code-block-pinching
requires:
  - all-dual-unique-neighbors-contract-operator-tails
  - one-anchor-grading-makes-parity-damage-quadratic
---

**Dead with the present scalar inputs.**  The proposal chooses thresholds,
replaces every coordinate in `U_t`, applies the exact one-anchor pinching and
sign correction to the complement, and iterates the all-local-dual tail
recurrence to successively smaller residual scales.

`hard-soft-thresholds-cannot-enter-anchor-contraction` proves that the two
required regimes are disjoint.  Cheap hard repair needs `t>>sqrt(E)`, while
making the optimistic quadratic remainder perturbative relative to the
linear contraction needs `t<<sqrt(E)`.  Moreover `(AUT2)` raises rather than
lowers thresholds and is vacuous on the diffuse RMS profile.

The route could be revived only by strengthening the scalar tail statement
to the operator-valued sparse fourth-moment/stopping estimate in
`sparse-anchor-odd-fourth-moment-is-the-renormalization-gate`, or by finding
a one-shot terminal exactification theorem that consumes an absolute
`o(1)` residual without iteration.  Neither follows from threshold
scheduling itself.

