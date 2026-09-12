---
rg: 2
id: shell-simple-neighborhood-kernel-proof
kind: route
title: Exhaust the neighborhood kernel by nested copies of V and kill it with one relator
target: shell-fp-stabilizer-forces-fp-germ-group
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
  - fp-quotient-iff-kernel-finitely-normally-generated
artifacts:
  - research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md
---

The shell realization proves that every isotropy germ at p has a
representative fixing p with singular set contained in {p}. Thus A_1->Q
is onto. A member of its kernel is locally V away from p and equal to
the identity near p. It is therefore locally V everywhere and belongs
to V by compactness and refinement of prefix tables. Hence

    K = union_(n>=1) R_n,       R_n=Fix_V(0^n*C).

The complement of 0^n*C is a nonempty finite union of binary cones.
A binary prefix partition of the full Cantor set with the same number
of cones identifies the supported group R_n with V. Each R_n is
nontrivial and simple. The sequence is nested and strictly increasing:
a nonidentity element supported in 0^n*1*C belongs to R_(n+1) and
not to R_n.

If N is a nontrivial normal subgroup of K, some N intersect R_n is
nontrivial. For every j>=n, N intersect R_j is then a nontrivial normal
subgroup of the simple group R_j, so R_j subset N. Their union is K.
Thus K is simple. Strict increase also proves it is not finitely
generated: any finite subset is contained in one R_n and cannot
generate R_(n+1).

Fix 1!=k in K. Since K is normal in A_1, the normal closure of k in
A_1 is contained in K; since K is simple, its normal closure already
under K is all of K. The normal closure under A_1 is therefore exactly
K. If A_1 has a finite presentation, adding the single relation k=1
presents A_1/K=Q. This proves the implication without assuming K
finitely generated as a subgroup.
