---
rg: 2
id: cayley-module-bilinear-certificate-proof
kind: route
title: Use translations and phases on the quotient Cayley module
target: cayley-module-bilinear-certificate-protects-pauli-mark
requires: []
---

On `H=ell^2(M_X)`, for `u in F_X` and `v in F_Z` define

```text
T_u delta_m = delta_(m+[u]),
S_v delta_m = (-1)^beta(m,[v]) delta_m.                       (CBR1)
```

Let `U_a delta_m=delta_(a m)`.  Invariance of `beta` gives

```text
U_a T_u U_a^-1=T_(a u),
U_a S_v U_a^-1=S_(a v),
[T_u,S_v]=(-I)^beta([u],[v]).                                (CBR2)
```

Send `x_i` to `T_(e_i)`, `z_j` to `S_(e_j)`, `J` to `-I`, and `a in A`
to `U_a`.  A same-basis prototype belonging to `R_X` maps to translation by
zero; one belonging to `R_Z` maps to the trivial phase.  Pure-X and pure-Z
commutators vanish.  Equation `(CBP2)` verifies every relation `(CBP5)`.
Thus all defining relators hold and `J` is nontrivial.

It remains to verify the criterion `(CBP4)`.  An invariant bilinear form on
`M_X times M_Z` is the same thing as a linear functional

```text
lambda:(M_X tensor M_Z)_A -> F_2,
lambda([u tensor v])=beta(u,v).                              (CBR3)
```

Necessity of `(CBP4)` follows by applying `lambda`.  Conversely `(CBP4)`
says that `c_q |-> b_q` is a well-defined linear functional on the span of
the finitely many prototype classes.  Extend it to all of `C` by a vector-
space basis.  Formula `(CBR3)` then gives the required invariant `beta`.

The presentation is finite because `A`, the module-relation generators, and
the mixed prototype list are finite.  Translating a prototype by `a in A`
is conjugation by `a`, so its relator area is one independently of the
address length.  Finally, any alleged contour consequence `J=1` would hold
in every representation, contradicting the representation above.
