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
  - simple-kazhdan-group-lacks-factorization-property
  - simple-kazhdan-lef-group-c-star-fails-llp
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
  - topological-full-group-embeds-in-subshift-elementary-group
  - no-decidable-group-contains-every-fp-rf-group
  - heisenberg-group-lies-in-no-z-subshift-elementary-group
  - separable-factors-hold-countably-many-subshift-groups
---

Assembly only: the root claim `simple-kazhdan-lef-groups-note-main-results` is, by definition, the
conjunction of the listed claims, so it holds exactly when each of them does. Nothing is
derived here beyond that conjunction; each derivation lives on the listed claim's own proof or
citation route.

The last eight members are the results revision 4.1 of `simple_kazhdan_sofic_group.tex`
(main 37551fd939) prints beyond the first thirteen:
- Theorem 2, the general engine for minimal topologically free actions with matricial crossed products;
- Corollary 3, the characterization of LEF groups as subgroups of simple Kazhdan limits of finite simple expanders;
- Corollary 4, one host per countable set of LEF groups, and the host for all recursively presented ones;
- the embedding of the derived topological full group in G_X;
- no host with solvable word problem contains every finitely presented residually finite group;
- SL_3(Z) lies in no G_X, through the Heisenberg group;
- a separable II_1 factor contains G_X for only countably many X.
