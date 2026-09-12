---
rg: 2
id: seven-point-regular-padding-refutes-short-row-derivability
kind: route
title: Compare two commuting involutions in the seven-point core and balance the marked factors
target: leavitt-small-anchors-do-not-force-the-native-p1-square
requires:
  - leavitt-has-an-explicit-finite-c-killing-certificate
  - leavitt-seven-cell-thompson-completion-requires-moved-pairs
artifacts:
  - research/artifacts/leavitt-small-anchor-p1-square-countermodel-2026-09-08.md
---

Take the existing seven-point cycle `C=(a b c)(d f e)` and
`B_1=B_2=Y=(b d)(f g)`. The choice `B_3=(a c)` satisfies both
small anchors but makes `p_1` a three-cycle and `B` a five-cycle.
Changing only `B_3` to `(c e)(b d)` also makes `B^3=(AB)^4=1`,
while `p_1=(a d b)(c g e)` still has order three. Both choices
commute with `Y` and use the same compiler occurrences throughout.

On the six-dimensional complement of the constant vectors, `C`
has each cube-root eigenvalue twice. Tensor with the regular
representation of `C_2^3` and give each marked `B_i` its own
central label. Every nonidentity marked second-factor element
then has trace zero, while the first factor also has its regular
profile. All compiler commutators have trivial central label.

The first choice has `p_1^2` defect one and `B^3` defect `sqrt(5/3)`.
For the stronger choice, the two disjoint three-cycles in `p_1^2`
have augmentation trace zero, giving square defect `sqrt(2)` in
dimension 48. Direct conjugation in the source formula gives
`rho_5=(a c d)(b e g)`, with the same nonzero defect. This
identifies an explicit failed row of `T_8` and preserves the
boundary of the strengthened normal-closure counterexample.
