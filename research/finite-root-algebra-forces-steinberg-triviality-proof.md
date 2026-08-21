---
rg: 2
id: finite-root-algebra-forces-steinberg-triviality-proof
kind: route
title: Root kernels form one two-sided ideal, while a finite involution algebra has finite root image
target: finite-root-algebra-forces-steinberg-triviality
requires: []
---

For `i!=j` put

```text
I_ij={a in L:pi(x_ij(a))=1}.
```

Root additivity makes `I_ij` an additive subgroup.  The standard Weyl words
in `St_n(L)` permute the type-`A_(n-1)` roots and carry `x_ij(a)` to
`x_kl(+/-a)`.  In characteristic two the sign is immaterial, so all `I_ij`
are one additive subgroup `I`.

Fix three distinct indices.  If `a in I` and `b in L`, the Steinberg
commutator relations give

```text
[x_12(a),x_23(b)]=x_13(ab),
[x_31(b),x_12(a)]=x_32(ba).
```

The left sides are trivial under `pi`; hence `ab,ba in I`.  Therefore `I` is
a two-sided ideal of `L`.  The binary Leavitt algebra is simple, so `I=0` or
`I=L`.  In the latter case every root subgroup is killed and, since the roots
generate the Steinberg group, `pi` is trivial.  In the former case every root
map is injective.  This proves the dichotomy.

Now suppose `A=pi(x_ij(L))''` is finite dimensional.  It is abelian because
the root subgroup is abelian.  Write `A~=C^m`.  Every root value is an
involution, and `C^m` has only `2^m` involutions.  Thus the root image is
finite.  Since `(L,+)` is infinite, its root map is not injective.  The
dichotomy forces `pi` to be trivial.

Finally, in the left regular representation the von Neumann algebra generated
by a subgroup is its subgroup von Neumann algebra.  Here
`x_ij(L)~=(L,+)` is an infinite elementary abelian two-group, so its dual is a
nonatomic Cantor probability group and its group von Neumann algebra is
diffuse.  This verifies directly that the canonical regular trace lies beyond
the finite-root hypothesis.
