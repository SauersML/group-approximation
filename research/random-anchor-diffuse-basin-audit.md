---
rg: 2
id: random-anchor-diffuse-basin-audit
kind: route
title: Audit tail peeling, nonlinear anchor rounding, and shared-face repair
target: random-anchor-contraction-does-not-yet-enter-the-diffuse-basin
requires:
  - all-dual-unique-neighbors-contract-operator-tails
  - operator-tail-contraction-misses-uniform-diffuse-matching
  - random-code-anchor-pinchings-contract-exact-transverse-energy
---

After tail peeling, retain the uniform diffuse regime on which the tail
recurrence is vacuous.  The exact anchor proof cannot be applied there
because it names the joint code-character PVM which synchronization is
supposed to construct.  Apply the universal one-anchor rounding estimate
instead: it bounds displacement and therefore bounds the increase of every
bounded-width residual, but triangle estimates yield no strict contraction.

Finally compare the two possible local repair operations.  Independent
face corrections break literal shared-coordinate equality, while a single
global correction constrained by all overlapping faces is the original
code-rounding problem.  The explicit two-dimensional sign-crossing family
shows why separate sign maps cannot be patched by a uniform coordinatewise
Lipschitz estimate.  These observations establish the stated fence and the
remaining global expected-energy target.
