---
rg: 2
id: disjoint-subgroup-flat-phase-factorization-proof
kind: route
title: Read the identity coefficient in a product of disjoint subgroup algebras
target: disjoint-subgroups-force-flat-finite-phase-marginals
requires: []
---

Let `lambda_g` denote the left regular unitary of `g in Gamma`. First take
finite sums

```text
z=sum_(f in F) a_f lambda_f,
y=sum_(m in M) b_m lambda_m.
```

The canonical trace extracts the coefficient of `lambda_1`. A product term
`lambda_f lambda_m` contributes to that coefficient exactly when

```text
f m=1.
```

Then `f=m^(-1)` belongs to `F intersect M`, so trivial intersection forces
`f=m=1`. Therefore

```text
tau(z y)=a_1 b_1=tau(z) tau(y).                         (DFP1)
```

For fixed `z in C[F]`, both sides of `(DFP1)` are norm-continuous in `y`.
The group algebra `C[M]` is norm dense in `C*_r(M)`, so `(DF1)` follows for
all `y in C*_r(M)`.

Now let `p in C[F]` be a projection and `v in C*_r(M)`. Since
`v v*,v* v in C*_r(M)`, traciality and `(DF1)` give

```text
||p v||_2^2
 =tau((p v)*(p v))
 =tau(v* p v)
 =tau(p v v*)
 =tau(p) tau(v v*),

||v p||_2^2
 =tau((v p)*(v p))
 =tau(p v* v p)
 =tau(p v* v)
 =tau(p) tau(v* v).                                     (DFP2)
```

If `F` is finite abelian, each character projection has identity coefficient
`1/|F|`, hence canonical trace `1/|F|`; substituting it into `(DFP2)` gives
the flat phase formula.

The proof uses neither amenability, Property `(T)`, nor finite dimensionality
of `M`. Finite dimensionality is needed only in applications that form a
polar by continuous functional calculus and want membership in the same
active algebra automatically. QED
