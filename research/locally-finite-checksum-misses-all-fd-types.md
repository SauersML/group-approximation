---
rg: 2
id: locally-finite-checksum-misses-all-fd-types
kind: claim
title: A summable checksum on a locally finite group misses finite-dimensional types of arbitrary size
distinct_from:
  noncommutative-checksum-misses-bounded-types: that uses compactness of one fixed unitary matrix size for an arbitrary group; this removes the dimension bound by using finite-subgroup multiplicity simplices and cross-amplification.
  finite-normalizer-star-no-go: that uses one finite packet's regular representation; this permits an infinite locally finite union and arbitrary irreducible dimensions.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that builds exact locally finite affine models for binary clone relations; this gives a general weighted covariance obstruction for every locally finite packet library, without assuming clone relations.
  toeplitz-finite-head-centralizes-deep-tail: that constructs the increasing finite Toeplitz head algebras; this proves those heads cannot provide an infinite-resolution checksum unless a tested word uses the non-locally-finite tail essentially.
---

ESTABLISHED.  Let `M` be a countable locally finite group, let
`(m_n)_(n>=0)` be a sequence in `M`, and let `a_n>=0` with
`sum_n a_n<infinity`.  Let `Omega` be any infinite set of pairwise
inequivalent finite-dimensional irreducible unitary representations of `M`;
their dimensions need not be bounded.

For every `epsilon>0` there are distinct `rho,sigma in Omega`, a common
dimension

```text
D=dim(rho) dim(sigma),                                  (LFC1)
```

and unitarily conjugate realizations on `C^D` of the cross-amplifications

```text
rhohat=rho^(direct_sum dim(sigma)),
sigmahat=sigma^(direct_sum dim(rho))                    (LFC2)
```

such that

```text
sum_n a_n ||rhohat(m_n)-sigmahat(m_n)||_(2,D)^2
 < epsilon.                                             (LFC3)
```

Consequently, on `pi=rhohat direct_sum sigmahat`, the unitary which swaps
the two `D`-dimensional summands has fine isotypic transport energy `2` but
weighted covariance energy less than `epsilon`, exactly as in
`(SNC3)--(SNC4)`.

Thus allowing noncommuting packet dimensions to grow does not rescue a
static heavy-tail checksum when all tested labels lie in one locally finite
group.  This applies to the union of the finite Toeplitz head groups
`GL_N(F_q)` (or any fixed-rank finite packet carried by those heads).  A
Toeplitz checksum which could feed
`multiscale-square-function-checksum-forces-hs-floor` must therefore contain
a load-bearing word involving the non-locally-finite tail, not merely
translate, enlarge, or reweight finitary head packets.
