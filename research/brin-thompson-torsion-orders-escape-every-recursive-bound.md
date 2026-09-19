---
rg: 2
id: brin-thompson-torsion-orders-escape-every-recursive-bound
kind: claim
title: The torsion-order and finite-subgroup profiles of 2V, and of every finitely generated group with solvable word problem containing 2V, exceed every recursive function
distinct_from:
  belk-bleak-2v-torsion-problem-is-undecidable: that is the imported undecidability of the torsion problem; this converts it into growth of the torsion-order and finite-subgroup profiles, which is the form the short-expander route to E consumes.
  brin-thompson-2v-is-torsion-locally-finite: that asks whether finitely generated torsion subgroups of 2V are finite; this is about how large short-generated finite cyclic subgroups of 2V are, and says nothing about local finiteness.
---

**ESTABLISHED** by `brin-thompson-torsion-orders-escape-every-recursive-bound-proof`
(lane proof; one import, verbatim; not independently reviewed; no priority
claimed).

**Statement.** Let `G` be a finitely generated group with solvable word problem
that contains a subgroup isomorphic to `2V`. Then for every recursive
`U: N -> N` there are infinitely many `L` with `TO_G(L) > U(L)`, and hence
`FS_G(L) > U(L)`. The profiles are those of
`finiteness-decidable-iff-finite-subgroup-profile-recursive`, for
any finite generating set.

`G = 2V` itself is allowed. Other examples are the Brin--Thompson groups `nV`
with `n >= 2`, which contain `2V` by acting on two of the `n` coordinates; this
containment and the solvability of their word problems are standard and are not
imported here.

**What it does and does not give.**
- *The necessary condition of the short-expander route holds in `2V`.* A host
  for that route must have `FS` beyond every recursive bound, equivalently an
  undecidable finiteness problem. `2V` has both. So the finite-subgroup
  obstruction that kills the Higman--Thompson groups (whose `FS` is recursive,
  by pumping in w10) does not reach `2V`.
- *It does not produce expanders.* The witnesses are cyclic, and cyclic
  subgroups are never short expanders of large order, by
  `abelian-finite-expanders-have-recursively-bounded-order`.
