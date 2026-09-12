---
rg: 2
id: deletion-pair-has-no-left-chart-coefficient-split
kind: claim
title: Every left finite-chart coefficient of the literal deletion pair has an exterior kernel
distinct_from:
  deletion-pair-has-no-right-chart-coefficient-split: That varies the coefficient in P_0[g]d f_0 and reduces input-sector maps to four normalized cases involving Psi_b; this varies the coefficient in P_0 c[g]f_0 and reduces target-sector maps to five pencils involving Psi_a. These are different one-sided coefficient families, and neither exclusion covers simultaneous left and right coefficients.
artifacts:
  - research/artifacts/kaplansky-lower-block-and-left-chart-exterior-formulas-2026-09-08.md
---

Use the reduced projectors f_0,P_0 and binary encoding of
K=GL_2(F_4). For the binary Leavitt units

    a=[[1,s_0],[t_0,0]], b=[[1,s_1],[t_1,0]], g=diag(a,b),

every c in F_2[K] gives a nonzero source kernel for P_0 c[g]f_0
in the natural boundary exterior square. Consequently there
is no group-ring identity L P_0 c[g]f_0=f_0, even with arbitrary
ambient support for L.

This is an exact algebraic exclusion for all left coefficients,
not just group elements or a bounded coefficient search. The
kernel may depend on c. The statement does not cover arbitrary
right coefficients between [g] and f_0, arbitrary incomparable
prefix pairs, or arbitrary transporters. No Kaplansky inverse
pair is supplied.

The right-coefficient family alone is separately excluded by
`deletion-pair-has-no-right-chart-coefficient-split`. Combining
the two statements does not exclude simultaneous left and
right corrections.
