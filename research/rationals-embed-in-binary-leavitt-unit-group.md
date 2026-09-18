---
rg: 2
id: rationals-embed-in-binary-leavitt-unit-group
kind: claim
title: The additive group of the rationals embeds in the unit group of the binary Leavitt algebra over F_2
distinct_from:
  rationals-do-not-embed-in-binary-leavitt-unit-group: that is the negation of this claim; this is the positive statement, recorded so that routes can consume it.
  integral-leavitt-unit-group-contains-q: that is (Q,+) in the integral Leavitt unit group, where the divisible element is a transvection of infinite order; over F_2 that transvection has order 2, so this needs a different element.
  tbar-embeds-in-laurent-leavitt-unit-group: that puts (Q,+) in the unit group of L ⊗ F_2[t^±1]; this asks for L itself.
---

**OPEN.** There is an injective homomorphism `(Q,+) -> U = L_(F_2)(1,2)^x`.

**Why it matters.** `U` is finitely presented (Khanh import, `leavitt-unit-group-finitely-presented`) and simple
(`binary-leavitt-unit-group-is-simple`). A yes would give a finitely presented simple group containing `Q`, after
`VA` and `2V`, and the first that is the full unit group of a ring. `(Q,+) <= GL_n(Q)`, so this is necessary for
`gl-n-q-embeds-in-binary-leavitt-unit-group`.

**Where it sits (lane gq-ring-alt, 2026-09-18).**
- *Sufficient:* an infinite-order unit conjugate to its diagonal copy
  (`infinite-order-leavitt-unit-conjugate-to-its-diagonal-copy`). A positive answer to Ara--Cortiñas
  Question 5.7 over `F_2` would give one (that claim's distinct_from note).
- *Necessary:* an element of infinite centralizer rank (`unit-roots-divide-centralizer-rank`), not conjugate to an
  infinite-order Thompson unit (`thompson-units-have-few-roots-in-leavitt-unit-group`). The span of the copy must
  lie in `[R,R]` (`leavitt-germ-traces-satisfy-frobenius`).
- *Calibration:* a proof of the negation answers Ara--Cortiñas Question 5.7 negatively over `F_2`, through
  `diagonal-copy-nonconjugacy-from-no-rationals` and `tensor-square-nonembedding-from-no-diagonal-conjugacy`. So a
  negative answer here is at least as hard as a negative answer to Question 5.7, and a positive answer to Question
  5.7 gives a positive answer here.

## Attempts

None beyond the reductions above.
