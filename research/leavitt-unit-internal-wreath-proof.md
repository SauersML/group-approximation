---
rg: 2
id: leavitt-unit-internal-wreath-proof
kind: route
title: Put block-monomial wreath products through the Leavitt prefix-code isomorphisms
target: leavitt-unit-internal-wreath-universality
requires:
  - wandering-leavitt-corner-reflection-compiler
artifacts:
  - GroupApproximation/Leavitt/PrefixCode.lean
---

Put `R=L_(F_2)(1,2)` and `U=R^x`.

## Finite wreath products

Let a finite group `F` act regularly on the finite set `X=F`.  For
`g=(g_x) in U^X`, let `D(g)` be the corresponding diagonal matrix in
`GL_X(R)`.  For `f in F`, let `P_f` be the permutation matrix of left
translation.  Then

```text
P_f D(g) P_f^(-1)=D(f.g),
```

so

```text
(g,f) |-> D(g)P_f                                      (IWP1)
```

is an injective homomorphism `U^X semidirectProduct F -> GL_X(R)`.
The complete prefix code with `|X|` leaves gives

```text
GL_X(R) ~= U.
```

Composing with this isomorphism embeds `W_F=U wr F` into `U`.

Equivalently, the diagonal matrix corners form one finite wandering Leavitt
corner orbit, so this is the finite instance of the wandering-corner
reflection compiler.

Every homomorphism from `W_F` to an MF group kills each coordinate copy of
`U`, because `Rad_MF(U)=U`.  It therefore kills the base `U^F` and factors
through the quotient `W_F->F`.  Conversely, `F` is finite and hence MF, so
this quotient detects every element outside the base.  This proves

```text
Rad_MF(W_F)=U^F.
```

Choose a nonidentity involution `d in U` and put it in the coordinate indexed
by the identity of `F`.  Simplicity of `U` says that `d` normally generates
that coordinate copy.  Conjugation by the regular `F`-factor moves this copy
through every coordinate, so

```text
normalClosure_(W_F)(d)=U^F.                              (IWP1a)
```

Let `N` be normal in `W_F`, and write `q:W_F->F`.  MF-target maps killing
`N` correspond exactly to MF-target maps from `F` killing `q(N)`.  The finite
group `F/q(N)` is MF, so the intersection of the latter kernels is `q(N)`.
Pulling back gives

```text
cl_MF^(W_F)(N)=q^(-1)(q(N))=N U^F.
```

Together with `(IWP1a)`, this proves the semantic-closure and quotient
classification formulas.

The same factorization proof works for the other target classes in the
claim.  Every homomorphism from `U` to a finite-dimensional linear group over
any field is trivial.  Maps to finite and residually finite groups are
therefore trivial as well, while Peter--Weyl point separation gives the same
conclusion for compact Hausdorff targets.  Hence every map from `W_F` to any
of these targets kills `U^F` and factors uniquely through `F`.  Because `F`
itself belongs to each target class, the quotient is exact in every case.
The universal MF quotient is invariant under group isomorphism, so
`W_F~=W_(F')` would force `F~=F'`.

Finite direct products preserve property `(T)`, and property `(T)` is
preserved by finite extensions.  Hence `W_F` is Kazhdan; it is finitely
generated for the same reason.  For nontrivial `F`, its radical is nontrivial
and proper.  Since the ambient group has full radical, intersecting the
ambient radical with `W_F` gives all of `W_F`, proving the strict subgroup
nonheredity formula.

## The finitary limit

Let

```text
w_i=1^i 0,                 p_i=s_(w_i)t_(w_i)            (i in N).
```

The words `w_i` are pairwise prefix-incomparable, so the idempotents `p_i`
are pairwise orthogonal.  A finitely supported tuple `g=(g_i) in U^(N)` is
sent to

```text
beta(g)=1+sum_i s_(w_i)(g_i-1)t_(w_i).                  (IWP2)
```

Orthogonality shows that `beta(g)^(-1)=beta(g^(-1))`, and cutting by
`t_(w_i)` and `s_(w_i)` proves injectivity.

For `sigma in Sym_fin(N)`, choose a finite invariant set `E` containing its
support and put

```text
v_sigma=1-sum_(i in E)p_i
          +sum_(i in E)s_(w_(sigma(i)))t_(w_i).         (IWP3)
```

Adding fixed points to `E` does not change the expression.  Prefix
orthogonality gives

```text
v_sigma v_tau=v_(sigma tau),
v_sigma beta((g_i)) v_sigma^(-1)=beta((g_(sigma^(-1)i))).
```

The diagonal subgroup `beta(U^(N))` fixes every `p_i`, whereas a nontrivial
`v_sigma` moves some `p_i`.  The two subgroups therefore assemble
injectively as

```text
U^(N) semidirectProduct Sym_fin(N) <= U.
```

Every MF-target homomorphism kills the base coordinatewise.  The quotient
`Sym_fin(N)` is locally finite and hence MF: each finite subset lies in one
finite symmetric group.  The quotient map therefore detects every element
outside the base, proving `(IW3)`.

The finitary symmetric group acts transitively on the coordinates, so one
nonidentity element of one simple coordinate normally generates the whole
base.  If `N` is normal in `W_infinity`, all MF-target maps killing `N`
factor through maps from `Sym_fin(N)` killing its image.  Every quotient of
a locally finite group is locally finite and hence MF.  The same pullback
argument as in the finite case therefore gives the final closure formula and
the one-word quotient criterion.
