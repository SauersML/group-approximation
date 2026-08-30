---
rg: 2
id: stw93-slice-si-survives-ambient-coefficients-proof
kind: route
title: Assign an orthogonal Jiang--Su plateau to every copy and every ambient coefficient
target: stw93-canonical-slice-ideal-has-infinite-cuntz-capacity
requires:
  - stw93-property-si-holds-on-the-jiang-su-central-slice
artifacts:
  - research/artifacts/stw93-mixed-slice-capacity-audit-2026-08-30.md
---

First consider a finite positive algebraic source

```text
y=sum_(j=1)^r x_j* iota(e_j) x_j,                       (2)
```

with `x_j in D` and positive contractions `e_j in E`.  Fix `n`.  Inside
`F(Z)`, choose `nr` pairwise orthogonal positive contractions

```text
f_(i,j),                 1<=i<=n, 1<=j<=r,
```

which are uniformly large in the property-(SI) sense.  As in
`stw93-orthogonal-z-targets-clone-kernel-cuts-proof`, these may be obtained
as disjoint plateau functions of a full-spectrum positive element in a
central copy of `Z` inside `F(Z)`.

Both `e_j` and `f_(i,j)` lie in `F(Z)`, and `e_j` is in its trace-kernel
ideal.  Same-slice property (SI) therefore gives `t_(i,j) in F(Z)` with

```text
t_(i,j)*t_(i,j)=e_j,          f_(i,j)t_(i,j)=t_(i,j).   (3)
```

Suppress `iota` in the following formulas and put

```text
s_i=sum_(j=1)^r t_(i,j)x_j,
F_i=sum_(j=1)^r f_(i,j).
```

Distinct plateau targets are orthogonal.  Equation `(3)` consequently
implies

```text
t_(i,j)*t_(k,l)=0 whenever (i,j)!=(k,l),
s_i*s_i=y,                 F_i s_i=s_i,
F_iF_k=0 whenever i!=k.                                  (4)
```

It follows that `b_i=s_i s_i*` are pairwise orthogonal and each is Cuntz
equivalent to `y`.  If `y!=0`, then the orthogonal positive contractions
`b_i/||y||` have sum below the unit and retain the Cuntz class of `y`.
Hence

```text
n[y]<=[1_D].                                             (5)
```

Now let `h in (K_Z)_+`.  The standard positive-cone description of a
generated ideal says that `h` is a norm limit of elements of the form `(2)`
(scalar normalizations can be absorbed into the `x_j`).  Given
`epsilon>0`, choose such a positive `y` with `||h-y||<epsilon`.  The standard
spectral-cut perturbation lemma gives

```text
(h-epsilon)_+ Cuntz-subequivalent to y.                  (6)
```

Combine `(5)` and `(6)` to obtain `(1)`.  Since the same construction works
for every `n`, every nonzero cut has infinite capacity.

The common-slice hypothesis is used exactly once: all `nr` target plateaus
must be mutually orthogonal before the witnesses are multiplied by the
ambient coefficients.  Slice-by-slice quasitrace annihilation does not
provide such a common orthogonal target family for generators coming from
different embeddings of `F(Z)`.
