---
rg: 2
id: jacobson-shift-positive-symbol-and-kernel-proof
kind: route
title: Generate every Laurent root and compare the two tail actions with the abstract quotient
target: jacobson-shift-literal-quotient-is-laurent-times-z
requires:
  - jacobson-shift-head-generates-normal-finitary-kernel
  - jacobson-shift-head-dies-in-amenable-targets
artifacts:
  - research/artifacts/jacobson-stable-letter-laurent-quotient-and-local-inner-action-2026-09-08.md
---

Sections 1--3 of the artifact extend the positive-tail symbol
from the original subgroup to the stable letter, whose symbol
is `z I_3`. Constants and `diag(z,z^(-1),1)` generate every
elementary Laurent matrix; elementary Euclidean row reduction
then gives all of `SL_3(R)`. Determinant separates the additional
central cyclic subgroup.

Identity positive symbol forces zero stable-letter exponent.
The negative tail is therefore also eventually fixed, so the
literal operator is finitary. This proves the symbol kernel
exactly equals `pi(L)`. Comparing with `Gamma/L=Lambda x Z`
identifies the literal kernel with `ker(kappa)`. The commutator
of a literal-kernel element with `t` lies both in `L` and in
`ker(pi)` and is therefore trivial.
