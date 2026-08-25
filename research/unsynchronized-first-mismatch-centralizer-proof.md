---
rg: 2
id: unsynchronized-first-mismatch-centralizer-proof
kind: route
title: Freeze one branch tail and apply properness of finite-mark centralizer area
target: unsynchronized-first-mismatch-area-is-centralizer-impossible
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Equation `(MTR6)` with `b` fixed proves that every `eta_a` centralizes the
fixed involution `beta`.  The root is nontrivial because its coefficient is
nonzero and the Steinberg group maps to the elementary group.

Take infinitely many tails whose resulting dual-prefix monomials are
distinct.  Equality of two `eta_a` modulo `<beta>` would identify an
`x_12` elementary matrix with either the identity or an `x_23` elementary
matrix.  Entry comparison makes both alternatives impossible unless the two
coefficients were equal.  The family therefore escapes through distinct
`<beta>`-cosets in `C_G(beta)`.

The proper centralizer-area theorem now forces the commutator areas of every
word section of those cosets to tend to infinity.  The canonical words
`eta_a` are one such section, proving the target.
