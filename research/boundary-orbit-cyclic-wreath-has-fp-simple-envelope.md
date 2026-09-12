---
rg: 2
id: boundary-orbit-cyclic-wreath-has-fp-simple-envelope
kind: claim
title: Cyclic lamps on a constant boundary orbit of a contracting group have a finitely presented simple envelope
artifacts:
  - research/artifacts/boone-higman-boundary-wreath-germ-construction-2026-09-08.md
---

Let G <= Aut(Y*) be a finitely generated contracting self-similar group,
where Y is a finite alphabet with |Y|>=2 and a distinguished letter 0.
Put p=0^infinity and
Omega_0=G*p. Then the restricted permutational wreath product

    W = (direct_sum_(r in Omega_0) Z) semidirect G

embeds in a finitely presented simple group.

When G contains an infinite-order element, adjoining one alphabet letter
gives an explicit faithful self-similar realization H of W. The group
E=V_(|Y|+1)(H) is finitely presented and has a faithful highly transitive
action on a countable set Omega with finitely presented finite pointwise
stabilizers. The twisted Brin--Thompson group Omega V_E is the required
simple envelope. The general case reduces to this one by taking the
product of G with the binary adding-machine group.

The proof is written in Cairn, not checked by Lean. This addresses the
specified boundary-orbit family; it is not a universal embedding theorem
for finitely generated groups with solvable word problem.
