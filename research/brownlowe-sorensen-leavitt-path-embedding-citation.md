---
rg: 2
id: brownlowe-sorensen-leavitt-path-embedding-citation
kind: route
title: Import Brownlowe--Sørensen Theorem 4.1 on embeddings of Leavitt path algebras of countable graphs in L_(2,R)
target: countable-graph-leavitt-path-algebras-embed-in-binary-leavitt
requires: []
artifacts:
  - research/artifacts/leavitt-pbh-general-2026-09-13.md
---

Citation import from N. Brownlowe and A. P. W. Sørensen, *Leavitt R-algebras over countable
graphs embed into L_(2,R)*, arXiv:1503.08705v3 (J. Algebra 454 (2016) 334--356). The PDF was
fetched on MSI on 2026-09-13 and converted with `pdftotext -layout`; line numbers refer to
that text. The extraction drops subscripts onto separate lines, restored here in brackets.
Not reproved here.

- **Notation** (l.22–27): "the Cuntz algebras O[n] are natural C∗-algebraic analogues of the
  Leavitt algebras LK(1,n) — they are universal for the same deﬁning relations (in each their
  category) and L[C](1,n) is dense in O[n]. Partly for this reason we denote L[K](1,n) by
  L[n,K] from here on out."
- **Abstract** (l.4–5): "For a commutative ring R with unit we show that the Leavitt path
  algebra LR(E) of a graph E embeds into L2,R precisely when E is countable."
- **Theorem 4.1** (l.396–401): "Let R be a commutative ring with unit and let E be a directed
  graph. If E is countable, then there is a ∗-algebraic embedding of the Leavitt path algebra
  L[R](E) into L[2,R], and if E0 is ﬁnite, then this embedding can be chosen to be unital. If E
  is uncountable then there is no embedding of LR(E) into L2,R as R-modules."

The same theorem is quoted on `leavitt-unit-groups-over-finite-fields-mutually-embed` as
credit for its prefix-code step.
