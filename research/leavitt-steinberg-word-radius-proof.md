---
rg: 2
id: leavitt-steinberg-word-radius-proof
kind: route
title: Build coefficient prefixes by balanced Steinberg commutator trees
target: leavitt-steinberg-quadratic-radius-pressure
requires:
  - leavitt-prefixes-form-exponential-heisenberg-packet
---

The finite presentation contains bounded words for roots over each ring
generator and bounded Weyl words permuting the five root indices. Split a
coefficient word into two nearly equal halves, realize the halves in roots
`ij` and `jk`, and use `(LWR2)`. A commutator has twice the sum of the two
input lengths, giving the displayed recurrence and the quadratic bound by
the Master theorem. Substitution into `(LHP5)` gives `(LWR3)`.
