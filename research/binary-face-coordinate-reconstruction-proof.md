---
rg: 2
id: binary-face-coordinate-reconstruction-proof
kind: route
title: Fourier-invert a binary joint PVM by its coordinate signs
target: binary-face-pvm-is-determined-by-coordinate-reflections
requires: []
---

On atom `P_b`, the factor `(I+(-1)^(a_i)Q_i)/2` acts as one when `a_i=b_i`
and zero otherwise.  Their product therefore acts as one exactly on `P_a`
and zero on every other atom, proving the reconstruction formula.  The
Lipschitz estimate is the telescoping bound for a bounded product of
contractions.
