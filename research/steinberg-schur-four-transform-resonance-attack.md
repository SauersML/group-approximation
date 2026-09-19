---
rg: 2
id: steinberg-schur-four-transform-resonance-attack
kind: route
title: Prove the rank-one Schur pivot through the proposed four-transform resonance equation
target: steinberg-rank-one-schur-pivot-is-invertible
requires:
  - steinberg-a-defect-isomorphism-on-rank-one-hasse-block
---

This route is invalidated by
`steinberg-schur-four-transform-reduction-fails-p-seven-check`.  The proposed
cofactor matrix omitted a binomial term and turned an anti-diagonal
correction into a diagonal one.  Its `p=7` determinant is zero even though
the original matrix has determinant `4`.  Any future Schur-pivot proof must
restart from the corrected cofactor `(S47F3)`, not from the four-transform,
parity, or `z |-> 4z` resonance equations.
