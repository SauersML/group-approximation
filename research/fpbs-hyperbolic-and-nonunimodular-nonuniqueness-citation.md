---
rg: 2
id: fpbs-hyperbolic-and-nonunimodular-nonuniqueness-citation
kind: route
title: Import Hutchcroft's hyperbolic and nonunimodular nonuniqueness theorems
target: fpbs-hyperbolic-and-nonunimodular-nonuniqueness
requires: []
artifacts:
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
---

Citation import, not a reproof.

* Tom Hutchcroft, *Percolation on hyperbolic graphs*, arXiv:1804.10191v3
  (submitted 2018-04-26, revised 2019-03-26).
* Tom Hutchcroft, *Non-uniqueness and mean-field criticality for percolation
  on nonunimodular transitive graphs*, arXiv:1711.02590v3.

Both identifiers, titles, authorship and abstracts were read from
`https://export.arxiv.org/api/query?id_list=<id>` on 2026-09-09. The
hyperbolic abstract gives `p_c<p_u` for nonamenable Gromov hyperbolic
quasi-transitive graphs together with the critical triangle condition; the
nonunimodular abstract gives `p_c<p_h<=p_u` for graphs whose automorphism
group has a nonunimodular quasi-transitive subgroup, and names `T_k x Z^d`.

**Statement read from the source, 2026-09-12.** The v3 TeX source
(`https://arxiv.org/e-print/1711.02590v3`, `NonunimodularPercolation_Revised5.tex`)
was read on MSI.
* Theorem 1.2 (`thm:pcpu`; Conjecture 1.1 shares its counter) reads: "Let G be a connected, locally finite graph,
  and suppose that Aut(G) has a quasi-transitive nonunimodular subgroup. Then
  p_c(G)<p_u(G)."
* The definitions that follow call `Gamma ⊆ Aut(G)` quasi-transitive if it has
  finitely many orbits on `V`. They call it unimodular if
  `|Stab_v u| = |Stab_u v|` for all `u, v` in one orbit, where `Stab_x y` is the
  orbit of `y` under the stabilizer of `x`.

So the theorem needs neither a transitive graph nor a transitive subgroup.

This route asserts only that the cited theorems say what the target records
them as saying. Neither paper proves the every-generating-set statement of
`fpbs-benjamini-schramm-universal` for an arbitrary nonamenable group.
