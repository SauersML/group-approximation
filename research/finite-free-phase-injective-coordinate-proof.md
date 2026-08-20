---
rg: 2
id: finite-free-phase-injective-coordinate-proof
kind: route
title: Intersect finitely many nontrivial normal subgroups of a free group
target: finite-free-phase-product-embedding-has-an-injective-coordinate
requires: []
---

The kernel of `(FPC1)` is

```text
ker(delta)=intersection_(i=1)^m ker(theta_i).             (FPC3)
```

We use the standard elementary fact that any finite intersection of nontrivial
normal subgroups of a nonabelian free group is nontrivial.  For two such
subgroups `A,B normal F`, choose nontrivial elements `a in A`, `b in B` which
do not commute.  Such a choice exists: otherwise `B` would lie in the cyclic
centralizer of `a`; a nonabelian free group has no nontrivial cyclic normal
subgroup.  Then

```text
[a,b] != 1,                  [a,b] in A intersection B.  (FPC4)
```

The intersection is itself normal, so induction proves the finite-intersection
statement.  In rank one, every nontrivial subgroup of `Z` has nontrivial
finite intersection, giving the same conclusion.

If every `theta_i` in `(FPC1)` were noninjective, all kernels in `(FPC3)`
would be nontrivial and their intersection would be nontrivial, contradicting
injectivity of `delta`.  Hence some coordinate is injective.  Reparametrizing
the image by that coordinate gives `(FPC2)`.
