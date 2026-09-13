---
rg: 2
id: operator-mf-group-not-weakly-quasidiagonal-exists
kind: claim
title: Operator MF does not imply weak quasidiagonality for countable groups
distinct_from:
  mf-to-weak-qd-citation-has-unproved-lifting-step: that audit shows the printed passage from MF to weak quasidiagonality is unproved, and exhibits an MF witness of C_2 with no positive extension; this shows the implication itself is false for a specific group.
  weak-qd-kazhdan-quotientless-group-is-trivial: that is the Ozawa--Thom consequence for weakly quasidiagonal Kazhdan groups; this uses it as the tool to rule out weak quasidiagonality.
artifacts:
  - research/artifacts/simple-kazhdan-lef-consequences-and-sources-2026-09-12.md
---

There is a finitely generated group which is LEF, hence operator MF (it embeds in the unitary
group of `prod_n M_(k_n) / sum_n M_(k_n)`), but which is not weakly quasidiagonal: it admits no
asymptotically multiplicative sequence of unital completely positive maps `C*(G) -> M_(d_n)`
separating the points of `G`.

The witness is `G = EL_3(LC(X,F_q) ⋊ Z)` for an infinite minimal subshift `X`.

So the introductory arrow "MF implies weakly quasidiagonal" of Dadarlat, arXiv:2007.12655v2, is
false as a statement about groups. The completely positive hypothesis in Proposition 3.19
(Ozawa--Thom) cannot be replaced by operator MF, or even by LEF.
