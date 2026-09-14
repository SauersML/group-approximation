---
rg: 2
id: non-rf-hyperbolic-from-residual-prime-torsion
kind: route
title: A hyperbolic group with prime torsion in its finite residual is not residually finite
target: non-residually-finite-hyperbolic-group
requires:
  - hyperbolic-group-trivial-radical-residual-prime-torsion
---

A prime-order element of `R_f(H)` is a nonidentity element killed by every
finite quotient, so `H` is not residually finite.

With `non-vtf-hyperbolic-via-residual-cyclic-filling` and
`residual-prime-torsion-via-free-factor` this closes the intended equivalence
cycle
`non-residually-finite-hyperbolic-group -> non-virtually-torsion-free-hyperbolic-group -> hyperbolic-group-trivial-radical-residual-prime-torsion -> non-residually-finite-hyperbolic-group`.
The cycle warning from `cairn check` is expected; do not delete a true
implication to silence it.
