---
rg: 2
id: collective-cofilling-is-common-erasure-cleaning
kind: claim
title: Collective cofilling is exactly common-support erasure cleaning
distinct_from:
  erasure-cleaning-rounds-all-projective-parity-valleys: that uses common-support cleaning to round projective operator models; this identifies the coding-theoretic hypothesis exactly and supplies explicit bounded-degree examples of the hypothesis alone.
  hamming-cosystolic-misses-hs-magnitude: that concerns ordinary nonabelian Hamming cosystolic expansion versus operator magnitude; this is a binary linear simultaneous-support equivalence.
---

Let `d: F_2^L -> F_2^M` be a based linear map and put `C=ker(d)`.
The following two statements, with the same constant `mu`, are equivalent.

1. For every finite family of attainable syndromes `beta_t in im(d)`, there
   are fillings `a_t` with

   ```text
   d a_t=beta_t,
   |union_t supp(a_t)| <= mu |union_t supp(beta_t)|.       (CCF1)
   ```

2. For every check set `E subset [M]`, there is one coordinate set `S(E)`
   such that

   ```text
   |S(E)| <= mu |E|,
   ker(d_(checks outside E)) <= C + F_2^S(E).              (CCF2)
   ```

Thus `(CCF2)` is not a new expansion notion: it is precisely the collective
cofilling property of Kaufman--Tessler, arXiv:2008.09495, Definition 2.1,
written for the based cochain map `d`.

In particular, their Theorem 1.5 gives explicit bounded-degree Ramanujan
complex families whose coboundary maps satisfy `(CCF2)` uniformly (bounded
degree makes their weighted and unweighted Hamming norms uniformly
equivalent).  This settles existence of bounded-degree Tanner maps with the
common-support cleaning property itself.  It does **not** yet give the code
needed by `erasure-cleaning-rounds-all-projective-parity-valleys`: positive-
degree constant-coefficient cocycle codes have bounded-weight coboundaries,
and hence fail ordinary linear distance.

Primary source: https://arxiv.org/abs/2008.09495
