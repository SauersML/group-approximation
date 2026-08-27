---
rg: 2
id: torsion-free-countable-non-mf
kind: claim
title: A torsion-free countable non-MF group
distinct_from:
  torsion-free-finitely-presented-non-mf: that root demands finite presentation; this claim drops it, and the two are joined by a torsion-free Higman embedding rather than by a new mechanism.
  torsion-free-higman-embedding: that claim is pure combinatorial group theory about presentations and says nothing about MF; this one is the analytic existence statement.
---

There is a torsion-free countable — ideally recursively presented — group
that is not MF.

By `mf-positive-controls` (subgroups of MF groups are MF), non-MF-ness
passes **up** to every overgroup.  Hence the finite-presentation
requirement in the root is not where the difficulty lies: any torsion-free
countable non-MF group placed inside a torsion-free finitely presented
group settles the root, and conversely every non-MF subgroup of a
torsion-free group is itself a torsion-free countable non-MF group.  So
this claim and the root are equivalent modulo
`torsion-free-higman-embedding`.

The same heredity is what kills the naive repair strategies for the root,
recorded there: covers do not work (non-MF does not pass down to a group
that surjects onto a non-MF group — free groups are residually finite,
hence MF, and surject onto everything), and embeddings of the existing
witness do not work (it contains an involution, so no torsion-free group
contains it).
