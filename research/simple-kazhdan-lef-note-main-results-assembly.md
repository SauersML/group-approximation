---
rg: 2
id: simple-kazhdan-lef-note-main-results-assembly
kind: route
title: The note's main results are the conjunction of the subshift theorem, marked limits, operator-algebra consequences, word-problem degrees and the embedding theorems
target: simple-kazhdan-lef-groups-note-main-results
requires:
  - simple-kazhdan-lef-group-from-minimal-subshift
  - infinite-simple-kazhdan-hyperlinear-group
  - finite-simple-groups-converge-to-simple-kazhdan-group
  - brown-mcduff-witness-for-simple-kazhdan-lef-group
  - every-turing-degree-is-a-simple-kazhdan-lef-word-problem
  - rf-groups-embed-in-simple-kazhdan-lef-groups
  - lef-groups-embed-in-simple-kazhdan-lef-groups
  - simple-kazhdan-lef-host-for-countably-many-rf-groups
  - universal-simple-kazhdan-lef-groups-exist
  - tower-simplicity-holds-for-topologically-free-actions
  - binary-el-simple-iff-minimal-topologically-free
  - topologically-free-matricial-crossed-el-simple-kazhdan-lef
  - lef-iff-subgroup-of-simple-kazhdan-finite-simple-limit
  - simple-kazhdan-lef-host-iff-lef-and-countably-many-types
  - simple-kazhdan-lef-host-for-recursive-lef-groups
  - lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts
  - lef-groups-have-simple-kazhdan-hosts-of-same-wp-degree
  - crossed-product-el-kazhdan-iff-finite-field-and-subshift
  - continuum-many-subshift-el-groups-pairwise-non-embeddable
---

Assembly only: the root claim `simple-kazhdan-lef-groups-note-main-results` is, by definition, the
conjunction of the listed claims, so it holds exactly when each of them does. Nothing is
derived here beyond that conjunction; each derivation lives on the listed claim's own proof or
citation route.

Revision 4.4 of `simple_kazhdan_sofic_group.tex` (main f34e9c0b1c, 8 pages) prints exactly the
members listed above:
- Theorem 1 on `G_X`, which answers `infinite-simple-kazhdan-hyperlinear-group`, and Theorem 2, the
  general engine for minimal topologically free actions with matrix models;
- Brown's formulation through the McDuff factor;
- Corollary 3, the characterization of LEF groups as subgroups of simple Kazhdan limits of finite
  simple expanders, together with its word-problem analogue: from revision 5.1 the host keeps the
  Turing degree of the word problem (`lef-groups-have-simple-kazhdan-hosts-of-same-wp-degree`),
  which contains the solvable case (`lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts`);
- the "Sharpness over Z" subsection of revision 5
  (`crossed-product-el-kazhdan-iff-finite-field-and-subshift`, in the `F_2`, `n = 3` form);
- Corollary 4, one host per countable set of LEF groups and the host for all recursively presented
  ones;
- Corollary 5, every Turing degree as a word problem degree and continuum many `G_X` none of which
  is isomorphic to a subgroup of another
  (`continuum-many-subshift-el-groups-pairwise-non-embeddable`).

Revision 4.4 dropped six results that revision 4.1 printed, to keep the paper short. They remain
established and reachable through the program themes, not through this root: the separable factor
count and the failure of the factorization property and of the LLP (structure and approximation
themes), `SL_3(Z)` lying in no `G_X` and no host with solvable word problem containing every
finitely presented residually finite group (embedding theme), and the embedding of the derived
topological full group in `G_X` (embedding theme).
