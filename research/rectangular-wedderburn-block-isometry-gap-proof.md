---
rg: 2
id: rectangular-wedderburn-block-isometry-gap-proof
kind: route
title: Rank-nullity leaves a fixed identity subspace in the Gram defect
target: rectangular-wedderburn-block-isometry-gap
requires:
  - regular-chart-wedderburn-coefficient-compiler
---

By the regular-representation multiplicity formula from the coefficient
compiler,

```text
rank(p_sigma)=d_sigma k,
rank(p_tau)=d_tau k.
```

Regard `X` as a linear map from `p_tau H_k` to `p_sigma H_k`.  Rank-nullity
gives

```text
dim ker(X) >= (d_tau-d_sigma) k.                      (RWG1)
```

On `ker(X)`, the positive Gram operator `X*X` vanishes while `p_tau` is the
identity.  Hence the self-adjoint operator

```text
p_tau-X*X
```

has eigenvalue `1` on a subspace of dimension at least `(d_tau-d_sigma)k`.
Its squared Frobenius norm is therefore at least that dimension.  Dividing by
the ambient matrix dimension `|G|k` gives

```text
||p_tau-X*X||_(2,ambient)^2
 >= (d_tau-d_sigma)/|G|.
```

Dividing instead by `rank(p_tau)=d_tau k` gives the corner-normalized version
`1-d_sigma/d_tau`.  This proves both inequalities and the claim.