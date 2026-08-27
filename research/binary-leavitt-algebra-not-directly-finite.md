---
rg: 2
id: binary-leavitt-algebra-not-directly-finite
kind: claim
title: The binary Leavitt algebra is not directly finite
distinct_from:
  augmentation-blocks-unital-leavitt-family: that says where the Leavitt relations can never be found, namely in any ring with a unital map to a domain; this is the elementary consequence of having them, that the one-sided inverse in the algebra itself is not two-sided.
  leavitt-group-algebra-not-stably-finite: that is the open demand for the same failure inside the group algebra F_2[R^x] at some matrix size; this is the established two-line fact about the Leavitt algebra itself, which is not a group algebra, and the whole difficulty of that node is the distance between the two.
  leavitt-gl-equals-el-and-perfect-unit-group: that is a K-theoretic statement inside the unit group, identifying GL with EL and proving perfectness; this is a statement about a single equation between four generators of the algebra, and neither uses the other.
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that is a soficity statement about the unit and elementary groups of d-ary Leavitt algebras over finite fields, proved through property (T) and a non-LEF witness; this is a ring identity in the binary algebra with no approximation content at all.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

In `R = L_(F_2)(1,2) = F_2<s_0,s_1,t_0,t_1 | t_i s_j = delta_ij,
s_0t_0 + s_1t_1 = 1>` one has

    t_0 s_0 = 1     and     s_0 t_0 != 1.

So `R` is a unital ring that is **not directly finite**: it carries a
one-sided invertible element that is not invertible.

This is the whole reason the Leavitt algebra is interesting for Kaplansky's
Direct Finiteness Conjecture, and it is also the reason it is *not* by itself
a counterexample: the conjecture is about group algebras `K[G]`, and `R` is
not one.  Everything in the surrounding lane is about how far the defect can
be moved toward a group algebra.  The two facts that carry it are
`leavitt-unit-group-algebra-surjects-onto-leavitt` (it moves onto a quotient
of `F_2[R^x]`) and `direct-finiteness-not-inherited-by-quotients` (a quotient
is not enough).

The same relations make `R` its own proper matrix amplification, `R = M_2(R)`
— see `leavitt-rank-three-unit-lift` — which is what defeats every
finite-rank argument in the neighbourhood.
