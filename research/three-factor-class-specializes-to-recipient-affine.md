---
rg: 2
id: three-factor-class-specializes-to-recipient-affine
kind: route
title: Recipient-affine rows are three-factor rows, so the three-factor assertion covers them
target: recipient-affine-three-factor-ca-are-surjunctive
requires:
  - three-factor-finite-alphabet-ca-are-surjunctive
artifacts:
  - research/artifacts/three-factor-audit-and-controlled-feedback-2026-09-12.md
---

A recipient-affine row `epsilon_i x_i(g) + B_i((x_j)_(j != i))(g)` is a finite
sum of terms with at most three unary lookup factors. The term
`epsilon_i x_i(g)` has one lookup, the identity, and `B_i` has at most three by
hypothesis. So every recipient-affine automaton lies in the three-factor class,
and the three-factor assertion makes it surjective whenever it is injective.

**This route closes a cycle on purpose.** With
`affine-normal-form-reduces-three-factor-surjunctivity` it forms a two-route
cycle, which records that the recipient-affine claim is equivalent to the
three-factor claim, and so to Gottschalk's conjecture, group by group. Do not
delete either route to silence the cycle warning; both implications are true.
