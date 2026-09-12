---
rg: 2
id: leavitt-nested-prefix-conjugacy-clique-proof
kind: route
title: Decompose a nested annulus into a left-comb prefix code
target: leavitt-nested-prefix-conjugacy-clique
requires:
  - murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness
---

Repeatedly use

```text
s_(0^ell)t_(0^ell)
 =s_(0^(ell+1))t_(0^(ell+1))
  +s_(0^ell 1)t_(0^ell 1).                             (NPP1)
```

Telescoping from `ell=j` to `k-1` gives

```text
e_j=e_k+sum_(ell=j)^(k-1)
             s_(0^ell 1)t_(0^ell 1).                  (NPP2)
```

In characteristic two, `(NPP2)` is `(NPC3)`.  Its summands are nonzero
orthogonal prefix projections, so `f_(j,k)` is a nonzero idempotent.

Put `M=k-j`.  Choose a complete prefix code
`beta_1,...,beta_M` below the prefix `1`; a binary left comb has exactly
`M` leaves for every `M>=1`.  Enumerate the target words

```text
alpha_r=0^(j+r-1)1,                 1<=r<=M.            (NPP3)
```

Define

```text
x=sum_r s_(alpha_r)t_(beta_r),
y=sum_r s_(beta_r)t_(alpha_r).                          (NPP4)
```

Prefix cancellation kills all cross terms, while completeness of the source
code and `(NPC3)` give

```text
yx=sum_r s_(beta_r)t_(beta_r)=q,
xy=sum_r s_(alpha_r)t_(alpha_r)=f_(j,k).                (NPP5)
```

Apply the explicit stabilized conjugator for `(NPP5)` and then a fixed Weyl
permutation of root indices.  This proves `(NPC5)` and hence the clique.
