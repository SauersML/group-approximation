---
rg: 2
id: two-raw-radical-reset-commutant-no-go-proof
kind: route
title: Compute the orthogonal complement of a nondegenerate hyperplane in the odd chart form
target: two-raw-radical-endpoints-cannot-both-centralize-a-symplectic-reset
requires:
  - every-predicate-has-s3-equivariant-raw-radical-drop
  - fanizza-radical-charts-admit-common-symplectic-reset-subgroups
---

The odd space has dimension `2n+1`, the chart form has rank `2n`, and a
reset hyperplane `W` has dimension `2n` with nondegenerate restriction.
Hence `W intersect W^perp=0` and dimension counting gives
`dim(W^perp)=1`.  The radical of the whole odd form is contained in
`W^perp`; both are lines, proving `(RRC3)`.

On the forbidden atom, `A_f(a)` kills the two-dimensional plane `R_a`.
The last row of `(RRC2)` cuts it by the one nonzero functional `ell`, so the
odd radical is exactly `R_a intersect ker(ell)`.  A represented packet word
commutes with the reset group precisely when its vector is orthogonal to
`W`; therefore at most this one radical line can enter the reset commutant.
For `ell_3`, both basis words evaluate to one and their sum evaluates to zero,
which gives `(RRC4)` and excludes both basis words individually.

The executable audit independently checks the same fact by projecting every
designated outside word along the odd radical.  Every projected vector is
nonzero in all marked crossed-chart blocks, so every endpoint word has a
nontrivial Pauli component on the reset spin factor rather than acting in its
multiplicity commutant.
