---
rg: 2
id: non-vtf-hyperbolic-via-residual-cyclic-filling
kind: route
title: Turn a non-residually-finite hyperbolic group into one with invisible torsion
target: non-virtually-torsion-free-hyperbolic-group
requires:
  - non-residually-finite-hyperbolic-group
  - hyperbolic-rf-question-equals-vtf-question
---

Direction (1) => (2) of `hyperbolic-rf-question-equals-vtf-question`.  Given a
word-hyperbolic `G` that is not residually finite, either its finite residual
already contains torsion, or a deep filling `G/<<g^(kj)>>` of a residual
element `g` of infinite order is word-hyperbolic and carries the image of `g`
as a nonidentity finite-order element of its own finite residual.

**Equivalence, not a reduction.**  Together with
`non-rf-hyperbolic-from-non-vtf-hyperbolic` this route forms a dependency cycle
between the two claims.  The cycle is intended: it records that the two
existence questions are one question.  `cairn check` warns about it, and the
warning must not be "fixed" by deleting either true implication; a least
fixpoint never establishes a claim through a cycle.
