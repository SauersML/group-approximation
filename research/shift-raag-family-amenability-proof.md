---
rg: 2
id: shift-raag-family-amenability-proof
kind: route
title: Reidemeister--Schreier along t and the complete-graph criterion for amenable right-angled Artin groups
target: shift-raag-family-classifies-amenability
requires: []
---

The map `G_J -> Z`, `t |-> 1`, `a |-> 0`, is well defined (every relator
is a commutator) and its kernel is the normal closure `N` of `a`.
Reidemeister--Schreier with transversal `{t^i}` gives generators
`a_i = t^i a t^-i` and relators `t^i [a, a_j] t^-i = [a_i, a_{i+j}]`,
`j in J`, `i in Z`.  So `N = A(Gamma_J)` and `G_J = N x| <t>` with `t`
the shift.

If `J = Z_{>0}` then `Gamma_J` is complete, `N` is free abelian on the
`a_i`, and `G_J = Z^{(Z)} x| Z = Z wr Z`, which is metabelian, hence
amenable.  If `d in Z_{>0} \ J`, the vertices `0` and `d` are not
adjacent, so `a_0, a_d` generate a free subgroup of rank two of the
right-angled Artin group (the parabolic subgroup on a full subgraph is a
retract, and the right-angled Artin group of two non-adjacent vertices is
`F_2`); hence `G_J` contains `F_2` and is neither amenable nor metabelian.
