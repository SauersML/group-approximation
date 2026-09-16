---
rg: 2
id: fpbs-acylindrically-hyperbolic-critical-l2-gap
kind: claim
title: Every Cayley graph of an acylindrically hyperbolic group has p_c below p_(2->2)
distinct_from:
  fpbs-sc-choi-seo: that imports Choi-Seo's stated conclusion p_c<p_u; this is the stronger strict l2 gap p_c<p_(2->2) on the same graphs, which the pivotal kernel bounds need and which Choi-Seo do not state as a theorem.
  fpbs-hyperbolic-nonunimodular-critical-l2-gap: that imports the strict l2 gap for Gromov hyperbolic graphs and graphs with a nonunimodular automorphism subgroup; this covers every Cayley graph of an acylindrically hyperbolic group, including non-hyperbolic ones such as surface mapping class groups containing Z^2.
  fpbs-free-product-cayley-graphs-have-critical-l2-gap: that proves the gap with explicit constants for free products on union generating sets; this gives no explicit gap but covers every finite generating set of every acylindrically hyperbolic group.
  fpbs-hyperbolic-quotient-fibre-estimates-l2-gap: that derives the gap from two fibre estimates for groups hyperbolic modulo an infinite normal subgroup; this uses no fibre structure and imports the two Choi-Seo estimates directly on Cayley graphs of acylindrically hyperbolic groups.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that conjectures a critical l2 bound on every nonamenable transitive graph; this proves a strict gap only for Cayley graphs of acylindrically hyperbolic groups.
  fpbs-critical-l2-implies-nonuniqueness: that is Hutchcroft's implication from an l2 hypothesis to nonuniqueness; this establishes the l2 hypothesis itself on a class of Cayley graphs.
artifacts:
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
---

Theorem A of `research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md`.

Let `G` be an acylindrically hyperbolic group and `S` a finite generating set
of `G`. Let `Gamma = Cay(G,S)` be the simple graph with an edge `{g,gs}` for
each `s in S union S^(-1)` with `s != e`. Then

    p_c(Gamma) < p_(2->2)(Gamma),

where `p_(2->2)` is the supremum of the `p` at which the connectivity matrix
`tau_p(u,v)` is bounded on `l2(G)`. Consequently `p_c(Gamma) < p_(q->q)(Gamma)`
for every `q in (1,infinity)` (arXiv:1804.10191, `prop:2to2givesqtoq`).

This is a deduction from imported theorems, not an independent verification.
It combines two sources:

* Choi–Seo, arXiv:2508.08932v2, prove Hutchcroft's two estimates (Gamma1) and
  (Gamma2) on every such `Gamma`.
* Hutchcroft's criterion `prop:criterion` in arXiv:1804.10191 turns those
  estimates into the gap.

Choi–Seo state only `p_c<p_u` and `nabla_(p_c)<infinity` as theorems, although
the prose at their line 242 treats the l2 boundedness as the underlying fact.
No explicit lower bound on `p_(2->2)-p_c` follows.
