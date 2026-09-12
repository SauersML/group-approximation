---
rg: 2
id: torsion-normal-generator-mf-character-criterion-proof
kind: route
title: Reblock the surviving torsion mark and take a trace limit
target: torsion-normal-generator-mf-character-criterion
requires:
  - torsion-normal-generator-has-full-support-corona-core
---

If `Rad_MF(G)=G`, every corona homomorphism represented by an operator-norm
asymptotic representation is trivial.  Hence every fixed group element
converges to the identity in operator norm and every resulting MF character
is one.

Conversely, if the radical is not all of `G`, some corona homomorphism is
nontrivial.  Since the finite-order element `a` normally generates `G`, its
image is nontrivial.  Apply active-core reblocking to obtain an
operator-norm asymptotic representation `sigma_n` and `c>0` with

```text
liminf_n ||sigma_n(a)-1||_2 >= c.                                  (1)
```

After a diagonal subsequence, the normalized traces converge on the
countable group.  Operator-norm asymptotic multiplicativity makes their
limit a conjugation-invariant positive-definite function.  For a unitary
`U`,

```text
||U-1||_2^2=2-2 Re tr(U).                                           (2)
```

Equations `(1)--(2)` give `Re chi(a)<=1-c^2/2<1`.  Thus the limit is a
nontrivial MF character, proving the converse.
