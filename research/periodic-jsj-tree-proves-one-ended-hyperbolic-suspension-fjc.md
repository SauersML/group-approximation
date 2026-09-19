---
rg: 2
id: periodic-jsj-tree-proves-one-ended-hyperbolic-suspension-fjc
kind: route
title: Apply the periodic JSJ tree and the acylindrical-tree Farrell--Jones theorem
target: one-ended-hyperbolic-suspensions-satisfy-fibred-fjc
requires: []
---

Source: Naomi Andrew, Yassine Guerch, and Sam Hughes,
*Automorphisms of relatively hyperbolic groups and the Farrell--Jones
conjecture*, Math. Ann. 395, article 89 (2026),
doi:10.1007/s00208-026-03431-7; Theorem A, proved in the one-ended case by
Theorem 5.21 and Corollaries 5.22--5.23.

Apply Theorem A to the relatively hyperbolic pair `(G,empty)`. Every
automorphism preserves the empty peripheral structure, and the peripheral
suspension hypothesis is vacuous.

The proof constructs the canonical JSJ tree `T^Per` relative to the
nonelementary periodic subgroups of the outer class of `Phi`. After
replacing `Phi` by a positive power, permitted by finite-index-overgroup
closure (Theorem 2.1(2)), Theorem 5.21 identifies the rigid vertex
stabilizers of `T^Per` exactly with the nonelementary periodic subgroups.
Corollary 5.22(2) then makes the induced action of `G_Phi` on `T^Per`
acylindrical.

Corollary 5.23 checks every vertex stabilizer. Elementary vertices give
virtually cyclic groups; QH-with-fibre vertices reduce through a finite
kernel to a hyperbolic 2-orbifold mapping torus, hence a 3-manifold-group
case; rigid vertices are periodic suspensions and satisfy `FJC_X` by
Lemma 2.6. Knopf's acylindrical-tree theorem, quoted as Theorem 2.5, now
yields `G_Phi in FJC_X`. The argument applies separately for
`X in {A,K,L}`. QED

The limitation is exact: Section 8, Conjecture 8.2 records the missing
relative-hyperbolicity input needed to remove the torsion/one-ended
restriction in the infinitely-ended case.
