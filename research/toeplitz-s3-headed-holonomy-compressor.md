---
rg: 2
id: toeplitz-s3-headed-holonomy-compressor
kind: claim
title: A Toeplitz head absorbs an external S3 and kills its sign character under compression
distinct_from:
  toeplitz-parity-compressor-candidate: that absorbs one external C2 by one head swap; this absorbs the full three-channel S3 symmetry and retains its sign as the parity twist.
  schur-packet-head-actuator-generates-over-tail: that makes one packet generator actuate the head; this embeds a complete nonabelian S3 in the deep-tail centralizer.
---

Let `T`, `sigma`, and the depth-`N` head `F_N~=M_N(F_2)` be as in
`toeplitz-head-tail-unital-self-embedding` and
`toeplitz-finite-head-centralizes-deep-tail`, with `N>=3`.  After increasing
the elementary rank, put

```text
Gamma=EL_r(T),                  beta=EL_r(sigma^N),
Lambda=Gamma x S_3.                                      (TSH1)
```

Let `s_0,s_1 in T^x` be the adjacent swaps of head coordinates `(0,1)` and
`(1,2)`, extended by the identity off the first three coordinates.  The
assignments

```text
c((01))=s_0 I_4,                 c((12))=s_1 I_4          (TSH2)
```

extend to a faithful embedding `c:S_3->Gamma`.  Its image is supported on the
finite head, centralizes `beta(Gamma)`, and has trivial intersection with it.
Consequently

```text
alpha(g,h)=(beta(g)c(h),1)                                (TSH3)
```

is an injective endomorphism of `Lambda`.  If
`chi(g,h)=sgn(h) in C_2`, then

```text
chi alpha=0.                                               (TSH4)
```

The group `Lambda` has property `(T)`.  Applying the parity-headed HNN
construction to `(alpha,chi)` produces a finitely generated recursively
presented group with a nontrivial central involution `J` which is killed by
every exact finite-dimensional unitary representation.

Unlike the one-swap compressor, `(TSH2)` retains a full nonabelian `S_3` in
one bounded head.  For the active-return application this external group is
to be identified with the **affine forbidden-point stabilizer** of
`affine-s3-endpoint-permutes-active-atoms`, not with the distinct `S_3` that
permutes the three radical charts in the six-generator packet.  It is
therefore an exact algebraic substrate for three-channel multiplicity
holonomy.  No normalized-HS collapse is asserted: the active endpoint
multiplicity algebra must still be coupled to the old `Lambda` commutant
rather than left on a tensor-independent factor.
