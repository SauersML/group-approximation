---
rg: 2
id: non-virtually-torsion-free-hyperbolic-group
kind: claim
title: A word-hyperbolic group that is not virtually torsion-free
distinct_from:
  non-residually-finite-hyperbolic-group: for one group, failing virtual torsion-freeness is strictly stronger than failing residual finiteness; as existence questions the two coincide by hyperbolic-rf-question-equals-vtf-question, and this node is the negative answer to Lück's question rather than to Gromov's
  hyperbolic-groups-virtually-torsion-free: that is the decision question; this is its negative answer, the counterexample
  hyperbolic-finite-residual-is-torsion-free: that is the positive universal assertion; this is the existence of a counterexample to it
---

Exhibit a word-hyperbolic group `G` with no torsion-free subgroup of finite
index.  By `finite-torsion-carrier-virtual-torsionfree-criterion` this is the
same as a word-hyperbolic group whose finite residual contains an element of
prime order.

This claim is equivalent to `non-residually-finite-hyperbolic-group`
(`hyperbolic-rf-question-equals-vtf-question`), and it is also equivalent to
the stronger shape `hyperbolic-group-trivial-radical-residual-prime-torsion`,
where the finite radical is trivial and the invisible torsion generates a
non-elementary normal subgroup.

## Attempts

- **From a non-residually-finite hyperbolic group.**
  `non-vtf-hyperbolic-via-residual-cyclic-filling` fills a residual element of
  infinite order deeply.  It is a complete derivation, so this claim is exactly
  as hard as Gromov's question and no easier.
- **Directly.**  A counterexample must supply a prime-order element killed by
  every finite quotient.  After `residual-prime-torsion-via-free-factor` one
  may assume trivial finite radical, and then
  `hyperbolic-prime-torsion-residual-dichotomy` forces that element to normally
  generate a non-elementary subgroup of the residual with full limit set.  No
  construction supplies such an element.  The Rips-kernel, relative-filling,
  persistent-class and non-sofic attacks recorded under
  `non-residually-finite-hyperbolic-group` transfer here unchanged, with the
  same missing inputs.
