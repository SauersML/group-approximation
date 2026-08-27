---
rg: 2
id: corona-defect-not-uniform-proof
kind: route
title: Balls of slowly growing radius, and no better
target: corona-defect-is-not-uniform
requires: []
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

A unitary of `Q` lifts to a unitary of `prod M_{d_n}`: lift to a contraction,
note `|| x_n^* x_n - 1 || -> 0`, and take polar parts for large `n`.  Fix such
lifts.  Because `Theta` is a homomorphism, each difference
`U_{gamma gamma'} - U_{gamma} U_{gamma'}` lies in the ideal, so its `n`-th
coordinate tends to `0` — this is the pointwise statement.

For the uniform statement, enumerate the group and let `B_R` be the ball of
radius `R` in a word metric.  Each `B_R` contributes finitely many pairs, so
there is a sequence `R_n -> infinity` with the defect over pairs in `B_{R_n}`
tending to `0` at coordinate `n`; that is all a corona representation gives.
Nothing forces `D_n -> 0`, and altering the lifts cannot repair it: two lifts
differ by an element of the ideal, which changes each coordinate by a term
tending to `0` pointwise and leaves the supremum over the infinitely many
pairs outside `B_{R_n}` untouched.  Truncating — setting `U_{gamma,n} = 1`
off `B_{R_n}` — makes the defect at the boundary of the ball equal to the
full distance between two unitaries, so it does not help either.

Uniform stability takes smallness of `D_n` as its hypothesis, so it has no
purchase here.  This argument is independent of the group class covered by
any particular uniform-stability theorem.
