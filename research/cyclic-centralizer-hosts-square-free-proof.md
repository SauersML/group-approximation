---
rg: 2
id: cyclic-centralizer-hosts-square-free-proof
kind: route
title: Short cycles force a cyclic support subgroup or a central element, and cyclic centralizers forbid both
target: cyclic-centralizer-hosts-have-square-free-kaplansky-graphs
requires:
  - kaplansky-graph-squares-force-central-trefoil-generators
  - zero-divisor-support-subgroup-host-constraints
---

Write `supp alpha = {1, h_2, h_3}` after left translation and put
`H = <h_2, h_3>`. By A--T Lemma 2.1, for least `beta` the equation
`alpha beta = 0` holds in `k[H]`. `H` is torsion-free with cyclic
centralizers, and it is not cyclic, since cyclic torsion-free groups are
abelian and their group rings are domains.

(1) **Lengths 2 and 3.** Two relations `a_1 g = b_1 g'` and `a_2 g' = b_2 g`
between the same vertices, and a 3-cycle, carry 4- and 6-tuples with the
same inequality pattern as in `kaplansky-graph-squares-central-trefoil-proof`.
The census `census2345.out` classifies them by explicit automorphisms of
`F(h_2, h_3)`:
- 18 tuples in 6 classes for length 2, all forcing `H` cyclic;
- 66 tuples in 13 classes for length 3, of which 9 force `H` cyclic and 4
  force `H` to be a quotient of `BS(1, +-1)`, `BS(1, +-2)` or the Klein bottle
  group, hence solvable. That contradicts item 3 of
  `zero-divisor-support-subgroup-host-constraints`.

This agrees with Schweitzer Thm 4.2 and A--T Thm 2.9 over `F_2`, and with
A--T's remark that the proof works over any field.

(2) **Length 4.** By `kaplansky-graph-squares-force-central-trefoil-generators`,
`H = <u, v>` with `u^3 = v^2 = z`, a nontrivial central element. The
centralizer of `z` in `G` is cyclic and contains `u` and `v`, so `H` is
cyclic. This contradicts the first paragraph.

(3) **Subgroups.** Centralizers in a subgroup are intersections of
centralizers with it, and subgroups of cyclic groups are cyclic. So the
hypothesis on `G` passes to `H`.
