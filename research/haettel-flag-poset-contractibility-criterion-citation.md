---
rg: 2
id: haettel-flag-poset-contractibility-criterion-citation
kind: route
title: Import Haettel's contractibility criterion as stated by Huang–Przytycki
target: haettel-flag-poset-contractibility-criterion
requires: []
---

Citation import, not a reproof. Read on 2026-09-13 from the arXiv LaTeX source of J. Huang and
P. Przytycki, arXiv:2509.06914, subsection "Haettel contractibility criteria", verbatim:

"Let S={s_1,…,s_n} be a totally ordered set. Let X be a simplicial complex of type S with the
induced relation on its vertex set, as defined in Section [chamber complex]: for vertices
x,x'∈X^0 we write x<x' if x,x' are neighbours and type(x)<type(x'). The following is a
consequence of [haettel2022link, §4.3, Thm B] and [haettel2021lattices, Thm 1.15].

Theorem. Let X be a simplicial complex of type S. Assume that (1) X is simply connected,
(2) the relation < on X^0 is a partial order, (3) for each x∈X^0, the collection of vertices
≥ x is bowtie free and upward flag, and (4) for each x∈X^0, the collection of vertices ≤ x is
bowtie free and downward flag. Then X is contractible."

The same criterion, with the same four hypotheses, appears in J. Huang, arXiv:2405.12068,
subsection "Two contractibility criterion for simplicial complexes". Definitions of bowtie free
and upward/downward flag: arXiv:2405.12068, definitions `def:flag` and the paragraph before
Lemma `lem:posets`.

Primary sources not read: T. Haettel, *Link condition for simplicial complexes, and CUB spaces*
(arXiv, "haettel2022link"), and T. Haettel, *Lattices, injective metrics and the K(π,1)
conjecture* ("haettel2021lattices").

Used by Huang–Przytycki in the proof of Lemma `lem:stpr` for the rank-4 almost spherical paths
with labels 434, 435 and 535, "whose hypotheses are satisfied by Theorems [tripleBn] and [flag]".
