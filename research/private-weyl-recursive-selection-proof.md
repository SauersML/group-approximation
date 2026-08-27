---
rg: 2
id: private-weyl-recursive-selection-proof
kind: route
title: Decide each finite sampler by real quantifier elimination and search
target: private-weyl-samplers-admit-recursive-selection
requires:
  - private-random-weyl-sampler-forces-growing-matrix-dimension
---

The simultaneous diagonal form for an elementary abelian representation
reduces all discrete choices to character lists in `(F_2^r)^d`.  After one
simultaneous conjugacy is removed, only one relative unitary remains.  Every
matrix entry of every sampled defect is a polynomial in that unitary's real
and imaginary coordinates with coefficients in `{0,+1,-1}`.  Therefore the
closed universal gap condition is a first-order sentence over the real
closed field and is decidable by Tarski quantifier elimination.

Choose the tested rational threshold below the strict empirical gap obtained
in the metric-entropy proof.  At least one candidate passes, so exhaustive
lexicographic search halts.  Running this independently for `r=1,2,...`
produces the recursive family.
