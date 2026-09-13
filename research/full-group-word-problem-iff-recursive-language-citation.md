---
rg: 2
id: full-group-word-problem-iff-recursive-language-citation
kind: route
title: Import of Grigorchuk–Medynets, J. Algebra 500 (2018), Theorem 1.1(3)
target: full-group-word-problem-iff-recursive-language
requires: []
artifacts:
  - research/artifacts/sk-novelty-prior-art-2026-09-13-part2.md
---

**Source.** R. Grigorchuk, K. Medynets, *Presentations of topological full groups by generators and relations*, J.
Algebra 500 (2018), 46–68, doi:10.1016/j.jalgebra.2016.10.027 (Crossref); arXiv:1508.04454.

**How it was read.** The arXiv PDF (latest version, fetched 2026-09-13) was extracted to text on MSI with `gs txtwrite`,
and the passages below were read there. The journal version was not compared.

**Verbatim.**
- Abstract: "We show that the word problem in a topological full group is solvable if and only if the language of the
  underlying subshift is recursive."
- Theorem 1.1(3): "The group G'_T has decidable word problem if and only if L(Ω) is recursive."
- Setting of Theorem 1.1: "Let (Ω,T) be a minimal subshift over a finite alphabet. Denote by G_T the topological full
  group of (Ω,T) and G'_T the commutator subgroup of G_T (Definition 2.1)."
- The introduction says the main result "is established in Theorem 4.1, Theorem 4.6, and Theorem 4.7".
- Corollary 3.7 gives the lower-bound mechanism: for `w = w_0⋯w_{n−1}` with `n ≥ 4`, "w ∈ L(Ω) iff" an explicit
  iterated commutator of generators equals 1 in `G'_T`.
