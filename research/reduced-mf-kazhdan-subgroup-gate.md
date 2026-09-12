---
rg: 2
id: reduced-mf-kazhdan-subgroup-gate
kind: claim
title: Reduced MF of a group from the known nonsoficity criteria makes an infinite Kazhdan group reduced MF
distinct_from:
  kt-double-reduced-cstar-is-mf: that asks reduced MF of one explicit double; this is the general descent to subgroups and the resulting Kazhdan gate for every group supplied by the criteria.
  reduced-mf-hyperlinear-radical-in-amenable-radical: that is what reduced MF buys (tracial visibility off the amenable radical); this is what reduced MF costs (MF reduced algebras of all subgroups).
---

ESTABLISHED.

1. For every group `G` and subgroup `H`, if `C*_r(G)` is MF then `C*_r(H)` is
   MF.
2. Every group satisfying the hypotheses of Kun--Thom Theorem A
   (`kt-pair-group-double-is-nonsofic`, `kun-thom-nonsofic-wreath`) or of the
   expander-matching criterion (`openai-expander-matching-criterion`)
   contains an infinite finitely generated Kazhdan subgroup `Gamma`.

So a nonsofic group produced by those criteria can have MF reduced C-star
algebra only if some infinite Kazhdan group does
(`infinite-kazhdan-group-with-mf-reduced-cstar`).  This applies in particular
to the binary Leavitt unit group and to the Kun--Thom wreaths and doubles.
