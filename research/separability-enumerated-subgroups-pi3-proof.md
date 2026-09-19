---
rg: 2
id: separability-enumerated-subgroups-pi3-proof
kind: route
title: Permutation representations for the upper bound, conjugate-basis subgroups for the lower
target: enumerated-subgroup-separability-is-pi3-complete
requires:
  - centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed
  - index-set-profinitely-closed-is-pi3-complete
---

The upper bound is the normal form in the claim body: finite-index
subgroups of a free group are exactly the stabilizers of a point in a
transitive finite permutation representation of the free group, an object
that can be enumerated, and containment of an enumerated subgroup in one
of them is a universal condition over the enumeration.

The lower bound is the composition of two established facts: the closure
computation `cl(A_J) = A_{cl(J)}` inside `F(a, b)` and the
`Pi^0_3`-completeness of closedness of enumerated index sets, together
with the observation that `e |-> (an enumeration of the generators of
A_{J_e})` is computable.

M. Hall's theorem, that finitely generated subgroups of free groups are
separable, is what makes the contrast sharp: the complexity is created
entirely by allowing infinitely many generators to appear over time.
