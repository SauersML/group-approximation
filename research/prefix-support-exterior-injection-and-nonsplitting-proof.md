---
rg: 2
id: prefix-support-exterior-injection-and-nonsplitting-proof
kind: route
title: Prove full tensor injection by finite prefix support and exclude splitting by augmentation
target: positive-shear-passes-exterior-test-without-projective-split
requires: []
artifacts:
  - research/artifacts/kaplansky-complete-exterior-injective-positive-shear-control-2026-09-08.md
---

The complete two-sector equations reduce to injectivity of
N=alt(I tensor I+s_1 tensor I+I tensor s_0). If NX=0, uniqueness
of coefficients at newly created support points forces the first
and second supports F,H to be disjoint. Prefixing one on F and
zero on H then permutes their finite union S.

For Q=X+X^transpose and the coordinate projection P onto F, the
kernel equation gives Q+hQ+Qh^transpose=0, while PQ+QP=Q.
Hence im(Q) is invariant under h and all conjugates of P. Those
conjugates read every binary digit and separate the actual tails
in S. Since every coordinate occurs in Q, this forces Q invertible.
But then I+h is similar to the invertible h^transpose, contradicting
the fixed all-ones vector of the finite permutation h.

The resulting natural exterior injection is separate from splitting.
All entries of g and its inverse belong to the free positive
coefficient algebra. Setting its generators to zero supplies a
finite subgroup representation with f_0 nonzero and P_0 zero.
Conditional expectation handles an ambient left inverse.
