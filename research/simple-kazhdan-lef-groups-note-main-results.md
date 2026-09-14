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
3. sits in the unitary group of a McDuff factor embeddable in `R^ω`, lacks the factorization
   property, and `C*(G_X)` lacks the LLP (`brown-mcduff-witness-for-simple-kazhdan-lef-group`,
   `simple-kazhdan-group-lacks-factorization-property`, `simple-kazhdan-lef-group-c-star-fails-llp`);
4. realizes every Turing degree as a word-problem degree
   (`every-turing-degree-is-a-simple-kazhdan-lef-word-problem`).

Embedding theorems built on the same tower argument:

5. every finitely generated residually finite group, and every finitely generated LEF group, is
   a subgroup of an infinite finitely generated simple Kazhdan LEF group
   (`rf-groups-embed-in-simple-kazhdan-lef-groups`, `lef-groups-embed-in-simple-kazhdan-lef-groups`);
6. one such group contains every group of a countable family of f.g. residually finite groups,
   for example every f.g. linear group (`simple-kazhdan-lef-host-for-countably-many-rf-groups`,
   `universal-simple-kazhdan-lef-groups-exist`);
7. the tower proof of simplicity needs only a minimal topologically free action
   (`tower-simplicity-holds-for-topologically-free-actions`,
   `binary-el-simple-iff-minimal-topologically-free`).

The status of this root is the conjunction of these claims; see the assembly route
`simple-kazhdan-lef-note-main-results-assembly`. Review state of each item lives on its own node
and in `research/artifacts/sk-review-*-2026-09-13-part*.md`.
