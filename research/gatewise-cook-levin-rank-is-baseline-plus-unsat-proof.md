---
rg: 2
id: gatewise-cook-levin-rank-is-baseline-plus-unsat-proof
kind: route
title: Sum the fixed-pivot gate ranks and restrict the resulting Clifford packet to its identity minor
target: gatewise-cook-levin-rank-is-baseline-plus-unsat
requires:
  - clifford-commutator-rank-is-packet-dimension
---

For AND, the determinant calculation in `(CLR1)` is

```text
det [[1,x],[y,z]] = z-xy = z+xy
```

over `F_2`.  The first row begins with `1`, so the matrix always has rank at
least one.  It has rank two exactly when its determinant is one.  Thus its rank
is `1+v_g`.  In each of the other three gate types, `(CLR2)` has one fixed
nonzero diagonal entry and a second diagonal entry equal to `v_g`, proving the
same formula.

Ranks add across block diagonal matrices, so

```text
rank_F2 R_C = sum_g rank_F2 R_g
            = sum_g (1+v_g)
            = m+UNSAT_C.
```

This proves `(CLR3)` for every assignment, including inconsistent assignments
of the internal wires.  The computation is over `F_2` inside each block, while
the final sum of block ranks is an integer sum; no cancellation modulo two is
possible.

For `(CLR4)`, select the first row and first column of every gate block.  The
selected `m x m` matrix is `I_m`.  In a fixed central-character sector, apply
`clifford-commutator-rank-is-packet-dimension` first to this baseline subgroup
and then to the group for `R_C`.  Their simple-module dimensions are `2^m` and
`2^(m+UNSAT_C)`, respectively.  The baseline sector algebra is the full matrix
algebra `M_(2^m)(C)`, so restriction of a full-packet simple is a direct sum of
its unique baseline simple.  Dimension comparison gives exactly
`2^(UNSAT_C)` copies.
