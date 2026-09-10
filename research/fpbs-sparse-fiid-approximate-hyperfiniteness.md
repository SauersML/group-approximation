---
rg: 2
id: fpbs-sparse-fiid-approximate-hyperfiniteness
kind: claim
title: Sparse FIID sets in exact groups admit uniformly bounded components after a small coupled cut
artifacts:
  - research/artifacts/fpbs/docs/sparse-base-surgery.md
---

For an exact countable group, every finite S and epsilon>0 admit
delta>0 and k<infinity such that any FIID vertex set E of density
at most delta has an invariant coupling C subset E with
P(1 in C)<=epsilon P(1 in E), and all components of Cay(Gamma,S)
on E minus C have size at most k. The cut is not asserted to be
a factor of the original labels. This is Fraczyk's Theorem 1.9,
arXiv:2512.09301v1, using Definition 1.8.

For an essentially free action presenting such a region U, Theorem
3.10 also provides a measurable cut V subset U with
mu(V)<=-11|S| epsilon log(epsilon) mu(U), for 0<epsilon<1/2,
and the same component bound k. This is a further cited input,
not a new derandomization theorem claimed here.
