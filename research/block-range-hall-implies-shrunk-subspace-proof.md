---
rg: 2
id: block-range-hall-implies-shrunk-subspace-proof
kind: route
title: Project every operator image to its block range-span
target: block-range-hall-implies-shrunk-subspace
requires: []
---

Take `A` satisfying `(BRH1)` and put

```text
X = direct_sum_(i in A) H_i.
```

For any `T in S` and `x=sum_(i in A) x_i in X`, the `j`-th target block of
`T x` is

```text
p_j T x = sum_(i in A) p_j T x_i in sum_(i in A) R_(j,i)=R_j(A).
```

Therefore every vector in `S(X)` lies in the orthogonal direct sum

```text
direct_sum_j R_j(A).
```

Hence

```text
dim(S(X)) <= sum_j dim(R_j(A)).
```

Since `dim(X)=sum_(i in A) dim(H_i)`, subtracting and using `(BRH1)` gives

```text
dim(X)-dim(S(X)) >= r.
```

Thus `X` is an `r`-shrunk subspace.  No choice of basis, genericity, or
independence between the rectangular blocks is used; overlaps of their ranges
are automatically credited through the dimensions of the sums `R_j(A)`.
