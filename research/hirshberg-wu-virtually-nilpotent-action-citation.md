---
rg: 2
id: hirshberg-wu-virtually-nilpotent-action-citation
kind: route
title: Import the long-thin-cover estimate for arbitrary virtually nilpotent actions
target: hirshberg-wu-virtually-nilpotent-action-bound
requires: []
---

Hirshberg--Wu,
[*Long thin covers and nuclear dimension*](https://arxiv.org/abs/2308.12504v2),
Corollary 10.6, states that if `V` is finitely generated and virtually
nilpotent and `X` is locally compact Hausdorff of finite covering dimension,
then every action satisfies

```text
dim_nuc(C_0(X) rtimes V)
    <= 2 * h(V)! * 9^d(V) * (dim(X^+)+1)^2.
```

For compact `X`, adjoining an isolated point does not change covering
dimension, so `dim(X^+)=dim(X)=r`; this is exactly `(HWV)`.  The source is
arXiv:2308.12504v2 (7 March 2024); the revision explicitly improves the
quantitative bounds in Section 10.
