---
rg: 2
id: bounded-local-group-relators-cannot-test-continuous-normalized-unitary-sum
kind: claim
title: Bounded-local group relators cannot test the continuous normalized unitary sum with constant soundness
distinct_from:
  rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm: that treats one arbitrary linear checker; this treats arbitrary nonlinear group words by telescoping and needs only bounded weighted leaf occurrence.
  raw-amitsur-permutation-sampling-has-factorial-gap-loss: that compares two noncommutative Amitsur Gram tables for proof-free samplers; this permits arbitrary auxiliary group-word proof coordinates and uses scalar unitary phase boundaries.
  simple-algebraic-pcp-binary-local-test: that has a discrete Boolean alphabet with a fixed symbol gap; this proves why the same local-testing statement fails for the continuous unit circle without a robust quantization layer.
---

ESTABLISHED.  Consider a group-word verifier with boundary unitaries
`t,v_1,...,v_N`, arbitrary auxiliary unitaries `z`, checks `w_c`, and
probability weights `p_c`.  Let `m_(c,i)` be the number of occurrences of
`v_i` or `v_i^(-1)` in `w_c`.  Assume constants `q,D` independent of `N`
such that

```text
sum_i m_(c,i) <= q,                  for every c,      (BLU1)
sum_c p_c m_(c,i) <= D/N,            for every i.      (BLU2)
```

Suppose the verifier has exact completeness for every scalar-unitary boundary
satisfying

```text
t=N^(-1/2)sum_i v_i:                                  (BLU3)
```

there are auxiliary scalar unitaries making every `w_c=1`.  Then it cannot
have a constant soundness lower bound against violation of `(BLU3)`.

Indeed take `N=k^2`, `k>=3`, and use the two scalar-unitary leaf vectors from
`rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm`.  With `t=1`, the good
vector has normalized sum one.  Exact completeness supplies one auxiliary
assignment `z_good`.  The bad vector has normalized sum zero, but

```text
(1/N)sum_i |v_i^bad-v_i^good|^2
 <=4/(k(k-1)).                                         (BLU4)
```

Reuse `z_good`.  Telescoping a unitary word and applying Cauchy--Schwarz give

```text
||w_c(bad,z_good)-1||_2^2
 <=q sum_i m_(c,i)|v_i^bad-v_i^good|^2.                (BLU5)
```

After averaging checks and using `(BLU2)` and `(BLU4)`,

```text
sum_c p_c ||w_c(bad,z_good)-1||_2^2
 <=4qD/(k(k-1))=O(1/N).                                (BLU6)
```

The boundary predicate error is nevertheless exactly one.  Thus no positive
soundness constant independent of `N` exists.  Unary finite-order relations,
nonlinear word products, and arbitrary auxiliary proof words do not help:
they are already included among the bounded-local checks and obey the same
telescoping estimate.

This is a no-go for a **generic** continuous normalized-sum compiler.  It does
not exclude a source-specific Amitsur verifier whose completeness is asserted
only on the particular noncommutative Fock boundary and not on every scalar
unitary solution of `(BLU3)`.  Such a surviving verifier must exploit that
source-specific Gram/incidence structure, or first impose a discrete alphabet
with a dimension-independent quantization gap.

