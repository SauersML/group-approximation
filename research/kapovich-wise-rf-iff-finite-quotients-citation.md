---
rg: 2
id: kapovich-wise-rf-iff-finite-quotients-citation
kind: route
title: Import the Kapovich--Wise equivalence of residual properties of hyperbolic groups
target: kapovich-wise-rf-iff-finite-quotients
requires: []
artifacts:
  - research/artifacts/hyperbolic-quotientless-kazhdan-proof-2026-09-11.md
---

Literature import.  I. Kapovich and D. T. Wise, *The equivalence of some
residual properties of word-hyperbolic groups*, J. Algebra 223 (2000),
562--583, DOI `10.1006/jabr.1999.8104`, Theorem 1.2.

Primary-source verification, 2026-09-11: the
[published paper uploaded by Ilya Kapovich](https://www.researchgate.net/publication/223118363_The_Equivalence_of_some_Residual_Properties_of_Word-Hyperbolic_Groups)
was read directly. Theorem 1.2, printed page 565, includes both nontriviality
qualifiers in its finite-quotient clause. Its proof is Theorem 3.3 on pages
570--571, using Lemma 3.1 and the combination theorem. Theorem 5.1 on pages
580--581 already establishes the residual-finiteness/virtual-torsion-freeness
equivalence; the repository's Osin filling argument is another proof of that
known equivalence.

This route imports the published theorem. The separate route
`kapovich-wise-via-g-subgroup` derives its finite-quotient equivalence from
the existing Olshanskii theorem, with every connective step supplied in the
artifact. Neither route claims an example of a non-residually-finite
hyperbolic group.
