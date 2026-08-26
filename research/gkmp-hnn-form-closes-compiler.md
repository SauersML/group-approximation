---
rg: 2
id: gkmp-hnn-form-closes-compiler
kind: route
title: An HNN form of GKMP permanence plus a separable benign subgroup makes the compiler MF-safe
target: mf-safe-finite-presentation-compiler
requires:
  - gkmp-amalgam-product-mf-permanence
  - gkmp-closes-fp-mf-completeness-modulo-hnn-and-separability
  - modular-machine-boone-group-is-mf
  - bidirectional-hnn-bridge-trivial-value-is-residually-finite
---

On the `INF` branch the rope output is `< G x C, s | s(l,1)s^-1 =
(l,phi(l))>` with `G` an exact MF machine group, `L <= G` separable (via a
virtually special ambient), and `C = B2(1)` residually finite MF.  An HNN
form of GKMP Theorem 1.1 (or an embedding of the rope output into a GKMP
amalgam) gives MF; on `FIN`, `E <= C` gives non-MF.
