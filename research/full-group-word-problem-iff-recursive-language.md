---
rg: 2
id: full-group-word-problem-iff-recursive-language
kind: claim
title: The derived topological full group of a minimal subshift has decidable word problem iff the subshift language is recursive
distinct_from:
  subshift-elementary-group-word-problem-degree: that node computes the Turing degree of the word problem of EL_3 over the subshift algebra; this one is the earlier decidability statement for the derived topological full group of the same subshift.
artifacts:
  - research/artifacts/sk-novelty-prior-art-2026-09-13-part2.md
---

Let `(Ω,T)` be a minimal subshift over a finite alphabet, let `G_T` be its topological full group, and let `G'_T` be the
commutator subgroup. Then `G'_T` has decidable word problem if and only if the language `L(Ω)` is recursive.

Source: Grigorchuk–Medynets, *Presentations of topological full groups by generators and relations*, J. Algebra 500
(2018) 46–68, Theorem 1.1(3).

Credit note for `simple_kazhdan_sofic_group.tex`. For the amenable simple group of the same subshift, this is the
decidability counterpart of the degree statement in `subshift-elementary-group-word-problem-degree`. The note should
cite it next to its own word-problem corollary (`research/artifacts/sk-novelty-proposal-2026-09-13.md`, P2).
