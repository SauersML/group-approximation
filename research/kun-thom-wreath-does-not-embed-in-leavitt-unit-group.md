---
rg: 2
id: kun-thom-wreath-does-not-embed-in-leavitt-unit-group
kind: claim
title: No Kun--Thom coset wreath over a Theorem E pair embeds in the binary Leavitt unit group
distinct_from:
  kun-thom-wreath-embeds-in-leavitt-unit-group: that is the embedding claim; this is its negation, carried as a separate node so that an obstruction route has a target.
  leavitt-unit-group-has-no-integer-heisenberg-subgroup: that is a subgroup obstruction about one small nilpotent group; this is the consequence for the wreath and for every group containing the Theorem E actor.
refuted_by:
  - kun-thom-wreath-embeds-in-leavitt-unit-group
---

**OPEN.** For every admissible Theorem E pair
`Gamma = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x_1^(+-1)..x_d^(+-1)]) semidirect SL_d(Z)`
with `r, d >= 3`, neither the coset wreath
`W = (direct_sum_(G/Gamma) Z/2) semidirect G` nor any group containing `G`
embeds in `Q = L_(F_2)(1,2)^x`. This includes the doubles `G *_Gamma G` and
`G *_Gamma (Gamma x Z)`.

**Consequence for the graph.** Once established, it removes the premise of
`leavitt-nonhyperlinear-via-kun-thom-wreath-embedding` for every parameter. The
Kun--Thom chain would then bear on `Q` only through a group with the same
hyperlinearity status that does not contain `G`.

Route: `kun-thom-wreath-nonembedding-from-no-heisenberg`.
