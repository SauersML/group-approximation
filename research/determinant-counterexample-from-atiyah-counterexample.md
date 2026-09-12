---
rg: 2
id: determinant-counterexample-from-atiyah-counterexample
kind: route
title: Move a torsion-free Strong Atiyah failure into the master host and read off a determinant failure
target: determinant-conjecture-counterexample-exists
requires:
  - algebraic-atiyah-and-determinant-one-group-tester
  - master-host-satisfies-algebraic-strong-atiyah
  - algebraic-strong-atiyah-counterexample-exists
---

Assume the master tester `E` satisfies Strong Atiyah over `Qbar`
([[master-host-satisfies-algebraic-strong-atiyah]]), and let a torsion-free
group `H` carry a matrix over `Qbar[H]` with non-integral kernel dimension
([[algebraic-strong-atiyah-counterexample-exists]]).  Consequence 2 of
[[algebraic-atiyah-and-determinant-one-group-tester]] gives a finitely
generated recursively presented torsion-free subgroup `K <= E` and an explicit
integral matrix over `Z[K]` with Fuglede--Kadison determinant below `1`.  So
[[determinant-conjecture-counterexample-exists]] holds, and the violating group
is nonsofic, as that claim requires.

The matrix is the restriction of scalars of a lifted stage matrix.  Its small
spectrum near `0` carries at least half of the fractional part of the kernel
dimension of the original matrix: the approximating stages hold that mass at
positive spectrum, and the limit collapses it into a fractional atom.
