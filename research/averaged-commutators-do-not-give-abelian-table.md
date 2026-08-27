---
rg: 2
id: averaged-commutators-do-not-give-abelian-table
kind: claim
title: Vanishing averaged generator commutators do not produce an approximate abelian group table
distinct_from:
  sparse-clifford-cycles-refute-average-commutator-rounding: that proves distance from every commuting generator tuple; this computes the multiplication defect of the canonical full-table word map and directly fences the uniform-abelian-stability reduction.
  all-abelian-uniform-hs-rounding-gives-global-pvm: that starts from an approximate multiplication table on every pair of source-group elements; this shows that averaged generator commutators do not supply that hypothesis.
  repeated-ldpc-shared-face-marginal-synchronization: that may still use the parity faces before constructing a table; this rules out discarding those faces after extracting only averaged pairwise commutation.
---

For `L=2m`, there are reflections `A_1,...,A_L` for which

```text
(1/L^2) sum_(i,j) ||A_i A_j-A_j A_i||_2^2 = 4/L,          (SGC1)
```

but the canonical ordered-word map from `F_2^L` has full-table
multiplication defect

```text
E_(a,b) ||phi(a)phi(b)-phi(a+b)||_2^2
   =2(1-2^(-m)) >=1.                                     (SGC2)
```

Thus there is no dimension- and length-independent modulus which turns
averaged generator commutator energy into the all-pairs approximate-
homomorphism hypothesis of uniform abelian HS stability.  In particular,
after synchronizing occurrence copies only in average, one cannot define
ordered products and invoke `all-abelian-uniform-hs-rounding-proof`: word
collection has a genuine, rather than merely telescoping, growing-length
loss.

This does not refute the repeated-LDPC synchronization claim.  Its parity
faces are load-bearing and would have to be used *before* manufacture of a
full group table.  The pairwise redundant-check overlay gives averaged
commutation data on shared representatives, but that datum by itself is
strictly weaker than an approximate representation of the finite abelian
code-dual group.
