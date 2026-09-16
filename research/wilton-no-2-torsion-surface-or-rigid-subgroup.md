---
rg: 2
id: wilton-no-2-torsion-surface-or-rigid-subgroup
kind: claim
title: A one-ended hyperbolic group without 2-torsion contains a surface subgroup or a quasiconvex infinite rigid subgroup
distinct_from:
  cyclic-graphs-of-free-groups-contain-surface-subgroups: that claim states Wilton's Theorem A for graphs of virtually free groups with virtually cyclic edge groups, and quotes Corollary B only in passing; this imports Corollary 6.4, the version with an infinite rigid subgroup, as its own statement
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for a surface subgroup unconditionally; this allows the alternative of an infinite quasiconvex rigid subgroup and assumes no 2-torsion
---

Import of Corollary 6.4 from H. Wilton, *Essential surfaces in graph pairs*, arXiv:1701.02505v3
(dated May 10, 2018).

Source: the arXiv PDF of v3, fetched 2026-09-16 and converted to text with `pdfminer`. The quotes
below undo line-break hyphenation and the `fi` ligature and change nothing else.

1. **Corollary 6.4** (Section 6), verbatim: "Every one-ended hyperbolic group without 2-torsion
   either contains a surface subgroup or contains a quasiconvex, infinite, rigid subgroup." The
   next sentence is: "In particular, Gromov's question is reduced to the rigid case (modulo the
   technical issue of 2-torsion)."
2. **Rigid**, as defined in Section 6, verbatim: "A group Γ is called rigid if it does not split
   over a (possibly finite) virtually cyclic subgroup."
3. **The input**, verbatim, immediately before Corollary 6.4: "Louder and Touikan showed that a
   hyperbolic group without 2-torsion has a finite hierarchy [29]. (The restriction on 2-torsion
   is technical, and conjecturally can be removed.)" Here [29] is L. Louder and N. Touikan,
   *Strong accessibility for finitely presented groups*, Geom. Topol. 21(3) (2017) 1805--1835.
4. **Surface subgroup**, as defined in the introduction, verbatim: "a subgroup isomorphic to the
   fundamental group of a closed surface of non-positive Euler characteristic."
   - Torus and Klein bottle groups contain `Z^2`, which does not embed in a hyperbolic group.
   - So in a hyperbolic group the surface has `chi < 0`, as the root claim requires.

Restated: if `Gamma` is a one-ended hyperbolic group with no element of order `2`, then `Gamma`
contains the fundamental group of a closed surface with `chi < 0`, or `Gamma` contains an
infinite quasiconvex subgroup which admits no nontrivial splitting over a finite or virtually
cyclic subgroup.

The letter version, Corollary B, says only "a quasiconvex rigid subgroup". Read literally that is
vacuous, since the trivial subgroup is rigid. Corollary 6.4 adds "infinite", which is the content
used here.
