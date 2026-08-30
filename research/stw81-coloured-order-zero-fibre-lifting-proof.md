---
rg: 2
id: stw81-coloured-order-zero-fibre-lifting-proof
kind: route
title: Pair base-cover colours with exactly lifted fibre colours
target: stw81-finite-base-usc-fibre-product-bound
requires:
  - stw81-zero-dimensional-usc-fibre-formula
artifacts:
  - research/artifacts/stw81-finite-base-usc-product-audit-2026-08-30.md
---

Fix a finite self-adjoint set `F subset A` and `epsilon>0`.  Choose
`h in C_c(X)_+`, `0<=h<=1`, such that

```text
||a-ha||<epsilon/3       for a in F,                    (1)
```

and set `K=supp(h)`.

## 1. Lift every fibre colour at one anchor

For each `x in K`, choose a nuclear-dimension approximation

```text
A_x --psi_x--> E_x=direct-sum_(l=0)^d E_x^(l)
    --phi_x--> A_x                                      (2)
```

which is within `delta` on `F_x`, with `psi_x` c.p.c., `phi_x` c.p.c., and
every `phi_x^(l)` c.p.c. order zero.  By the Winter--Zacharias cone
correspondence and projectivity of cones over finite-dimensional algebras,
each colour lifts through `A->A_x` to a c.p.c. order-zero map

```text
Phi_x^(l):E_x^(l)->A.                                   (3)
```

Put

```text
b_(x,a)=sum_l Phi_x^(l)(psi_x(a_x)^(l))-a.              (4)
```

At `x`, this element has norm less than `delta`.  Upper semicontinuity
therefore gives a neighborhood `U_x` on which

```text
||(b_(x,a))_y||<2delta       for a in F.                (5)
```

Finitely many `U_x` cover `K`.

## 2. Add the base colour coordinate

The covering-dimension refinement theorem gives a finite refinement
`(V_i)` of a neighborhood of `K`, anchors `x_i` with
`closure(V_i) subset U_(x_i)`, and a colour map

```text
c(i) in {0,...,n}
```

such that closures of distinct equal-colour sets are disjoint.  Choose a
partition of unity `(f_i)` on a neighborhood of `K`, subordinate to this
refinement, and put `g_i=hf_i`.  Then

```text
sum_i g_i=h,
g_i g_j=0       if i!=j and c(i)=c(j).                 (6)
```

Let `E=direct-sum_i E_(x_i)` and define

```text
Psi(a)=(psi_(x_i)(a_(x_i)))_i,
Phi^(c,l)((z_i)_i)
 =sum_(i:c(i)=c) g_i Phi_(x_i)^(l)(z_i).                (7)
```

Here coordinates not belonging to `(c,l)` are omitted.  The incoming map
`Psi` is c.p.c.  Each map `Phi^(c,l)` is c.p.c. order zero: central
multiplication preserves order zero, and `(6)` makes distinct summands in
one base colour orthogonal.

Nuclear dimension requires the individual colour restrictions to be
c.p.c., not their sum.  For every `y`, the partition-of-unity calculation
using `(5)` gives

```text
||(Phi Psi(a)-ha)_y|| <=2delta.                         (8)
```

Choose `delta<epsilon/3` and combine `(1)` and `(8)`.  This proves the upper
bound in `(FBP1)`.  The lower bound follows because every evaluation
`A->A_x` is a quotient.

## 3. Simple-fibre shadows

Let `D=A/J`, and let `C subset D` be commutative hereditary.  As in the
zero-dimensional proof, every quotient fibre `D_x` is zero or `A_x`, and a
nonzero fibre `C_x` forces `A_x` to be elementary.  Inside `K(H)`, a
commutative hereditary subalgebra has vector-space dimension at most one.
Writing `C=C_0(Y)`, the structure map `pi:Y->X` is therefore injective.

On each compact neighborhood `N subset Y`, the continuous injection
`pi|N` is a homeomorphism onto a compact subspace of `X`.  Hence
`dim(N)<=n`.  Covering dimension is local for second-countable locally
compact spaces, so `dim(Y)<=n`, as claimed.
