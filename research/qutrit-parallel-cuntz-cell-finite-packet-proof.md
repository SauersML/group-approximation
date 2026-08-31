---
rg: 2
id: qutrit-parallel-cuntz-cell-finite-packet-proof
kind: proof
title: Count the shared-center parallel Cuntz packet and its scalar covariance
target: qutrit-parallel-full-cuntz-cell-covariance-is-finite
requires:
  - qutrit-full-cuntz-four-root-cell-is-finite-but-generates-full-leavitt-group
  - finite-overgroup-packing-preserves-hyperlinearity
---

## Shared-center normal form

Let

```text
S=span{s_0,s_1},       T=span{t_0,t_1},
P=span{s_rt_s:r,s in {0,1}}.
```

Their dimensions over `F_2` are `2,2,4`. For an intermediate
coordinate `j_a` set

```text
X_a(u)=x_(i,j_a)(u),          Y_a(v)=x_(j_a,k)(v).
```

If `a!=b`, all roots in the `a` cell commute with all roots in the
`b` cell. Within one cell,

```text
[X_a(u),Y_a(v)]=Z(uv),        Z(w)=x_(ik)(w).            (QPC6)
```

The crucial point is that the range root `Z(w)` has no `a` label. It is
the same matrix for every intermediate coordinate. Thus

```text
[U_(a,r),V_(a,s)]=Z(s_rt_s)
                 =[U_(b,r),V_(b,s)],                    (QPC7)
```

which is the explicit relation between distinct scalar-conjugate cells.

Move all `X` roots left, all `Y` roots next, and the common central
root last. Every word has the form

```text
product_a X_a(u_a) product_a Y_a(v_a) Z(w).             (QPC8)
```

In the active `(m+2)`-coordinate matrix, the `(i,j_a)` and
`(j_a,k)` entries recover `u_a` and `v_a`. After those are known, the
`(i,k)` entry recovers `w`. Hence the form is unique and

```text
|M_m|=|S|^m |T|^m |P|
     =2^(2m)2^(2m)2^4=2^(4m+4).                        (QPC9)
```

The common center contains

```text
A=Z(s_0t_0+s_1t_1)=Z(1).
```

As in the one-cell calculation, an element of `M_m` is scalar only if
all `u_a,v_a` vanish and `w` is `0` or `1`. Therefore

```text
M_m intersect K=<A>.                                    (QPC10)
```

## Finite scalar covariance

Let `Sigma_m` be the scalar permutation group of the coordinates
`j_1,...,j_m`, conjugated back from the `h`-normal basis. Since `h`
is the identity on its fixed block, `Sigma_m` centralizes `h`. It
fixes `i,k`, hence fixes every `Z(w)`, and acts on `M_m` by

```text
sigma X_a(u) sigma^(-1)=X_(sigma(a))(u),
sigma Y_a(v) sigma^(-1)=Y_(sigma(a))(v).                (QPC11)
```

Thus

```text
B_m=M_m semidirect Sigma_m
```

is a finite group of order `2^(4m+4)m!`. If `d sigma in B_m` is a
scalar matrix, then `d=(d sigma)sigma^(-1)` lies in
`M_m intersect K=<A>`. Conversely `A` and `Sigma_m` are scalar.
This proves

```text
B_m intersect K=<A> times Sigma_m.                      (QPC12)
```

All factors commute with `h`. Put

```text
H_m=<h> times B_m,
E_m=<h,A> times Sigma_m.
```

The scalar-module decomposition also gives `C intersect E_m=<h>`.
Indeed an element of `C` not in `<h>` has nontrivial action on the two
nonfixed `h`-types; the factors `A` and `Sigma_m` are supported in the
`h`-fixed block and cannot cancel that action. Equations `(QPC10)` and
`(QPC12)` give

```text
H_m intersect K=E_m.                                    (QPC13)
```

## The finite graph model

The actual matrices satisfy every relation in `(QPC7)` and
`(QPC11)`, so there is a surjection

```text
K *_(E_m) H_m -> <K,M_m>=EL_28(L).                      (QPC14)
```

The last equality already follows from any one cell. Both vertices and
the edge on the left are finite. Its fundamental group is virtually
free, residually finite, sofic, and hyperlinear.

For completeness, its qutrit Hecke table agrees with the concrete table.
Take any active root `v=X_a(s_r)` or `Y_a(t_r)`. In an amalgam normal
form, `v c v^(-1)` with `c in C` can return to the `K` vertex only when
`c in C intersect E_m=<h>`. Since `v` centralizes `h`,

```text
C intersect vCv^(-1)=<h>.                               (QPC15)
```

Thus its character graph is

```text
2alpha'+beta'=2alpha+beta
```

and every compatible block has squared norm `1/27`. Regular finite
quotients of the virtually free cover retain the uniform character
weights `1/9`, the common four-dimensional center, the scalar return
`A`, and all permutation covariance.

This proves a genuine multi-cell firewall, not just one-cell repetition.
The relations `(QPC7)` are explicit words in the kernel of the naive
one-cell amalgam map, and `(QPC11)` identifies the cells as literal
`K`-conjugates. Yet their complete covariant closure is one finite
vertex packet. A nonparallel incidence must make a central output root
serve as a noncentral input root in a later cell; parallel Morita
squares cannot create the required trace imbalance.
