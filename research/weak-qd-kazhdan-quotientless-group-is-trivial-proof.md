---
rg: 2
id: weak-qd-kazhdan-quotientless-group-is-trivial-proof
kind: route
title: Apply the exact Ozawa--Thom hypothesis and separate an element in its quotient
target: weak-qd-kazhdan-quotientless-group-is-trivial
requires: []
artifacts:
  - research/artifacts/operator-mf-weak-quasidiagonality-audit-2026-09-11.md
---

Import Proposition 3.19 of
[Dadarlat, arXiv:2007.12655v2](https://arxiv.org/html/2007.12655v2),
attributed there to Ozawa--Thom: an infinite weakly quasidiagonal Kazhdan
group has an infinite residually finite quotient. The approximation
hypothesis of the target is precisely Definition 3.10 in that paper.

If `G` were infinite, obtain a quotient `q:G->Q` as above. Choose `x!=1`
in `Q`, and by residual finiteness choose `f:Q->F` to a finite group with
`f(x)!=1`. The composite `f q`, considered as a map onto its image, would
be a nontrivial finite quotient of `G`. Hence `G` is finite. Its identity
map then forces it to be trivial. Section 4 of the artifact records the
same proof with the convention boundary stated explicitly.
