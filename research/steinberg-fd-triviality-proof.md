---
rg: 2
id: steinberg-fd-triviality-proof
kind: route
title: Combine root torsion with simplicity of the Leavitt algebra
target: steinberg-cover-fd-triviality
requires: []
---

Let `pi:St_r(L)->U(n)`.  In characteristic two each root subgroup
`x_ij(L)` is an elementary abelian two-group.  Its commuting involutive
image is simultaneously diagonalizable and therefore finite (at most
`2^n` elements).  The additive kernel in each root consequently has finite
index.  Intersecting over the finitely many pairs gives a finite-index
additive subgroup `A<=L` such that `x_ij(A)` lies in `ker(pi)` for all
`i!=j`.

The Steinberg commutator relations and normality of the kernel imply

```text
x_kj(la)=[x_ki(l),x_ij(a)] in ker(pi),
x_ik(al)=[x_ij(a),x_jk(l)] in ker(pi)
```

for distinct indices.  Iterating shows that every root element with
coefficient in the two-sided ideal `LAL` is killed.  Because `A` has finite
additive index it is nonzero; hence `LAL` is a nonzero ideal.  The binary
Leavitt algebra is simple, so `LAL=L`.  Every root subgroup is killed, and
the root subgroups generate `St_r(L)`.  Thus `pi` is trivial.

Any representation of `EL_r(L)` pulls back along the Steinberg quotient,
so it is trivial as well.  An exact atlas criterion solution would yield a
nontrivial finite-dimensional representation (faithful on its A8 chart),
contradicting the theorem.
