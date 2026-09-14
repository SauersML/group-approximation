---
rg: 2
id: simple-kazhdan-lef-groups-note-main-results
kind: claim
title: Root of the simple Kazhdan LEF groups note — the main results of simple_kazhdan_sofic_group.tex and the embedding theorems built on them
root: true
distinct_from:
  infinite-simple-kazhdan-hyperlinear-group: that is the existence question of Brown, Ozawa and Pestov; this is the program root collecting everything the note proves about the subshift groups, including that answer, the marked limits, the operator-algebra consequences, the word-problem degrees and the embedding theorems.
  kazhdan-elementary-approximation-type-mirrors-ring-type: that is the unification program root over arbitrary simple rings; this is the root of one manuscript about crossed products of minimal subshifts and the groups they host.
  simple-kazhdan-lef-groups-note-open-questions: that root collects the questions the note leaves open; this root collects its theorems.
---

**Program root (sk swarm, 2026-09-13).** The results stated in or planned for
`simple_kazhdan_sofic_group.tex` ("Infinite simple Kazhdan groups that are limits of finite
simple groups"). For every infinite minimal subshift `X`, `G_X = EL_3(LC(X,F_2) ⋊ Z)`:

1. is infinite, finitely generated, simple and Kazhdan, and LEF, so sofic and hyperlinear
   (`simple-kazhdan-lef-group-from-minimal-subshift`), which answers
   `infinite-simple-kazhdan-hyperlinear-group`;
2. is the marked limit of the finite simple groups `SL_{3N}(F_2)`, whose Cayley graphs form
   expanders (`finite-simple-groups-converge-to-simple-kazhdan-group`);
3. sits in the unitary group of a McDuff factor embeddable in `R^ω`, which is Brown's form of the
   question (`brown-mcduff-witness-for-simple-kazhdan-lef-group`);
4. realizes every Turing degree as a word-problem degree
   (`every-turing-degree-is-a-simple-kazhdan-lef-word-problem`), and continuum many `G_X` are
   pairwise non-embeddable (`continuum-many-subshift-el-groups-pairwise-non-embeddable`).

Embedding theorems built on the same tower argument:

5. every finitely generated residually finite group, and every finitely generated LEF group, is
   a subgroup of an infinite finitely generated simple Kazhdan LEF group
   (`rf-groups-embed-in-simple-kazhdan-lef-groups`, `lef-groups-embed-in-simple-kazhdan-lef-groups`),
   and the host can be chosen so that its word problem has the Turing degree of the input's
   (`lef-groups-have-simple-kazhdan-hosts-of-same-wp-degree`), in particular with solvable word
   problem exactly when the input has one (`lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts`);
6. one such group contains every group of a countable family of f.g. residually finite groups,
   for example every f.g. linear group (`simple-kazhdan-lef-host-for-countably-many-rf-groups`,
   `universal-simple-kazhdan-lef-groups-exist`);
7. the tower proof of simplicity needs only a minimal topologically free action
   (`tower-simplicity-holds-for-topologically-free-actions`,
   `binary-el-simple-iff-minimal-topologically-free`);
8. over `Z` the subshift hypothesis is sharp: for a homeomorphism `T` of a Cantor set `X`,
   `EL_3(LC(X,F_2) ⋊_T Z)` is simple and Kazhdan iff `(X,T)` is conjugate to a minimal subshift
   (`crossed-product-el-kazhdan-iff-finite-field-and-subshift`, the "Sharpness over Z" subsection
   of revision 5).

The status of this root is the conjunction of these claims; see the assembly route
`simple-kazhdan-lef-note-main-results-assembly`. Review state of each item lives on its own node
and in `research/artifacts/sk-review-*-2026-09-13-part*.md`.

**Scope, 2026-09-14.** This root tracks what the manuscript prints. Revision 4.4 (main f34e9c0b1c,
8 pages) shortened the paper to its main results, so six results it no longer prints left this
root and stay established under the program themes: the separable factor count, the failure of the
factorization property and of the LLP, `SL_3(Z)` lying in no `G_X`, no host with solvable word
problem containing every finitely presented residually finite group, and the embedding of the
derived topological full group in `G_X`. Revision 5 (main 911b7b3f4a, 11 pages) added the
sharpness statement (item 8) and revision 5.1 (main 37ebf96798) the Turing-degree form of the
host theorem (item 5), both now members of the assembly. The rigidity theorem
`subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence` is established but is not printed in
the note. Revision 5.3 (main 6493524c09) dropped the note's self-posed questions at the user's
request; the note ends with the finitely presented case only, and the program questions below
stay in this graph under `simple-kazhdan-lef-groups-note-open-questions`.
