---
rg: 2
id: virtually-free-by-cyclic-groups-contain-no-bs-one-n
kind: claim
title: A virtually finitely generated free-by-cyclic group contains no Baumslag--Solitar group BS(1,n) with |n| >= 2
distinct_from:
  virtually-free-by-cyclic-groups-satisfy-boone-higman: that is the Boone--Higman theorem for this class; this is an elementary subgroup obstruction saying which groups the class cannot contain.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports Boone--Higman for BS(m,n) and for free-by-cyclic groups; this shows the second family never contains BS(1,n) with |n| >= 2.
---

**ESTABLISHED** through `virtually-free-by-cyclic-no-bs-one-n-proof`. The
argument is elementary and no novelty is claimed.

**Statement.** Let `G` have a subgroup of finite index isomorphic to
`F_k ⋊ Z` with `k` finite. Then `G` has no subgroup isomorphic to
`BS(1,n) = <b, c | c^-1 b c = b^n>` for any `|n| >= 2`.

**Use.** A group containing `BS(1,2)` lies outside
`virtually-free-by-cyclic-groups-satisfy-boone-higman`. One example is the
Druţu--Sapir one-relator group, `drutu-sapir-group-satisfies-boone-higman`.
