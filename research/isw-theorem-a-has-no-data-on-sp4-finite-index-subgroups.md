---
rg: 2
id: isw-theorem-a-has-no-data-on-sp4-finite-index-subgroups
kind: claim
title: Ioana--Spaas--Wiersma Theorem A admits no input data on any finite-index subgroup of Sp4(Z)
distinct_from:
  isw-theorem-a-has-no-data-on-sp4-lattice: that fences the ambient lattice Sp_4(Z) only; this fences every finite-index subgroup Gamma', where a refutation could equally run because the LLP of C*(Gamma') and of C*(Sp_4(Z)) stand or fall together, and whose realizable classes need not extend to Sp_4(Z).
  sp4-finite-index-fd-projective-multiplier-is-finite: that is the arithmetic finiteness of the realizable classes; this is its consequence for the ISW Theorem A hypotheses, through pointwise closedness of coboundaries.
  sp4-contains-no-isw-affine-subgroup: that excludes the infinite-index affine subgroups on which ISW Corollary B runs; this excludes Theorem A itself on every finite-index subgroup, relative to ANY subgroup Lambda.
---

**THEOREM.**  Let `Gamma' <= Sp_4(Z)` have finite index and let
`Lambda <= Gamma'` be ANY subgroup.  There is no sequence
`c_n in Z^2(Gamma',T)` such that

```text
(1) c_n|_Lambda is not a 2-coboundary, for every n;
(2) c_n(g,h) -> 1 for every g,h in Gamma';
(3) each c_n is the exact cocycle of a finite-dimensional
    projective unitary representation of Gamma'.              (NA1')
```

These are the scalar hypotheses of Ioana--Spaas--Wiersma Theorem A
(arXiv:2006.01874, p. 2), recorded as `(NA1)` in
`isw-theorem-a-has-no-data-on-sp4-lattice`.  Their remaining hypothesis,
relative property (T) of `(Gamma',Lambda)`, is free: `Gamma'` is a
finite-index subgroup of the Kazhdan group `Sp_4(Z)`, so it has
property (T).  Consequently Theorem A cannot refute the LLP of
`C^*(Gamma')` for any finite-index `Gamma'`, any `Lambda`.

**Why the ambient fence was not enough.**  The LLP of a full group
C*-algebra passes to subgroups (ISW Remark 1.2) and returns from
finite-index subgroups (Fournier-Facio--Willett arXiv:2603.18456v2,
Theorem 3.39).  So a refutation of `sp2g-z-full-c-star-algebra-has-llp`
at `g = 2` could run on any congruence subgroup `Gamma(N)`.  A
projective representation of `Gamma(N)` need not extend to `Sp_4(Z)`, so
`isw-theorem-a-has-no-data-on-sp4-lattice` — whose cocycles live on the
whole lattice — said nothing about such data.  The cocycle supply
`(NA1')(3)` is what fails at every finite index:
`sp4-finite-index-fd-projective-multiplier-is-finite`.

**What survives on the scalar side.**  Theorem A on INFINITE-index
subgroups `H <= Sp_4(Z)` carrying infinitely many realizable classes and
a relative-(T) pair.  The affine ones (the Corollary B shape
`Z^2 x| Sigma`) are excluded by `sp4-contains-no-isw-affine-subgroup`.
The operator-valued Theorem C mouth is untouched
(`sp4-isw-theorem-c-embeddable-twist-data-exists`).
