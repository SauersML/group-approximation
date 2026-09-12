---
rg: 2
id: affine-gate-matrix-rank-proof
kind: route
title: Read the gate violation bit off a two-by-two determinant
target: affine-gate-matrix-rank-counts-violated-gates
requires: []
---

**Complete direct proof.**

A `2 x 2` matrix over `F_2` with a nonzero row has rank `1` when its
determinant vanishes and rank `2` otherwise.

For the AND gate, `R_and = [[1,x],[y,z]]` has first row `(1,x)`, never zero,
and `det R_and = z - xy = z + xy` over `F_2`.  The gate is consistent exactly
when `z = xy`, so `det R_and = v_g` and `rank R_and = 1 + v_g`.

For COPY, NOT and XOR the violation bit is the affine expression listed in the
claim, and `diag(1, v_g)` has rank `1 + v_g` for the same reason.

Entries: `1, x, y, z` and `1, 0, v_g` are affine-linear in the wire bits in
both cases.

`(AGR2)` is `rank(P direct sum Q) = rank P + rank Q`, summed over the `m`
gates, with `sum_g v_g = UNSAT_C` by definition of the violation count.
