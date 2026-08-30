---
rg: 2
id: stw81-clopen-order-zero-lifting-proof
kind: route
title: Lift fibre colours exactly and assemble them over disjoint compact-open pieces
target: stw81-zero-dimensional-usc-fibre-formula
requires: []
artifacts:
  - research/artifacts/stw81-zero-dimensional-usc-field-audit-2026-08-30.md
---

Put

```text
d=sup_(x in X) dim_nuc(A_x).
```

If `d=infinity`, fibre quotient monotonicity already proves `(ZUF1)`.
Assume `d<infinity`.  Fix a finite self-adjoint set `F subset A`, let
`M=max(1,max_(a in F)||a||)`, and fix `epsilon>0`.

## 1. Compact-open reduction

Nondegeneracy of the `C_0(X)`-action gives `f in C_c(X)_+` with

```text
||a-fa||<epsilon/3       for a in F.
```

A zero-dimensional locally compact space has a basis of compact-open sets.
A finite union of such sets gives a compact-open `K` containing `supp(f)`.
For the central projection `z=chi_K`,

```text
||a-za||<=||a-fa||<epsilon/3.                            (1)
```

## 2. Exact lifts at one anchor

Fix `x in K`.  Since `dim_nuc(A_x)<=d`, choose a finite-dimensional algebra

```text
E_x=direct-sum_(l=0)^d E_x^(l),
```

a c.p.c. map `psi_x:A_x->E_x`, and a c.p.c. map
`phi_x:E_x->A_x` such that each restriction `phi_x^(l)` is c.p.c. order zero
and

```text
||phi_x psi_x(a_x)-a_x||<delta       for a in F.         (2)
```

The two external inputs are the order-zero cone correspondence and
projectivity of finite-dimensional cones.  Winter--Zacharias,
[*Completely positive maps of order
zero*](https://arxiv.org/abs/0903.3290), Corollary 3.1, identifies c.p.c.
order-zero maps `E->B` with star-homomorphisms
`C_0((0,1]) tensor E->B`.  For finite-dimensional `E`, this cone is
projective; equivalently, order-zero maps out of `E` lift through arbitrary
quotients, as recorded in Kirchberg--Winter,
[*Covering dimension and
quasidiagonality*](https://arxiv.org/abs/math/0207164), Remark 2.4.

Apply this to the quotient `A->A_x`.  Each colour has a c.p.c. order-zero
lift

```text
Phi_x^(l):E_x^(l)->A.                                   (3)
```

Set

```text
H_x=sum_l Phi_x^(l)(1),
b_(x,a)=sum_l Phi_x^(l)(psi_x(a_x)^(l))-a.              (4)
```

At the anchor, `(H_x)_x=phi_x(1)<=1` and (2) gives
`||(b_(x,a))_x||<delta`.  Fibre-norm functions of an arbitrary
`C_0(X)`-algebra are upper semicontinuous.  Therefore, for fixed
`eta>0`, there is an open neighborhood `U_x` on which simultaneously

```text
||(H_x)_y||<1+eta,
||(b_(x,a))_y||<2delta       for a in F.                 (5)
```

No lower semicontinuity or continuous-field assumption is used.

## 3. Disjoint clopen assembly

Finitely many `U_x` cover the compact set `K`.  Zero-dimensionality gives a
finite pairwise-disjoint compact-open partition

```text
K=disjoint-union_(j=1)^m V_j,
V_j subset U_(x_j).                                     (6)
```

Let `z_j=chi_(V_j)`, central projections in `M(A)`.  Put

```text
E=direct-sum_j E_(x_j),
Psi(a)=(psi_(x_j)(a_(x_j)))_j,
s=(1+eta)^(-1),
Phi^(l)((c_j)_j)=s sum_j z_j Phi_(x_j)^(l)(c_j).         (7)
```

The map `Psi` is c.p.c.  Multiplication by a central projection preserves
complete positivity and order zero.  Equal-colour summands for distinct
`j` have orthogonal supports, so every `Phi^(l)` is c.p.c. order zero.

The sum `Phi=sum_l Phi^(l)` is also contractive.  Fibrewise it vanishes off
`K`; on `V_j`, (5) gives

```text
Phi(1)_y=s(H_(x_j))_y<=1.
```

Thus `Phi:E->A` is c.p.c. and `d`-decomposable.

For `y in V_j`, equations (5) and (7) give

```text
||Phi Psi(a)_y-a_y||
 <=s||(b_(x_j,a))_y||+(1-s)||a_y||
 <2delta+eta M.                                         (8)
```

Both `Phi Psi(a)` and `za` vanish off `K`.  Choose `delta,eta` with
`2delta+eta M<2epsilon/3`; combine (1) and (8).  This proves
`dim_nuc(A)<=d`.  Evaluation `A->A_x` supplies the reverse inequality.

## 4. Simple fibres and commutative hereditary shadows

Assume every nonzero `A_x` is simple.  The established simple-algebra
nuclear-dimension trichotomy says each fibre dimension is `0`, `1`, or
`infinity`; its supremum has the same form.

Let `D=A/J` be a quotient and let `C subset D` be commutative hereditary.
The quotient is again an upper-semicontinuous `C_0(X)`-algebra and

```text
D_x=A_x/closure(J_x),
```

so simplicity makes `D_x` either zero or `A_x`.  Central multiplication
preserves `C`, making it a commutative `C_0(X)`-algebra.  Since everything
is separable, choose a strictly positive `c in C`; then

```text
C_x=closure(c_x D_x c_x),                               (9)
```

so `C_x` is commutative hereditary in `D_x`.

If a nonzero `C_x` sits in a simple fibre, it is full.  A full commutative
hereditary subalgebra makes that fibre Morita equivalent to a commutative
simple algebra, hence elementary.  Conversely a hereditary subalgebra of
`K(H)` is `K(H_0)` and is commutative only when `dim(H_0)<=1`.  Therefore

```text
dim_C(C_x)<=1       for every x.                         (10)
```

Write `C=C_0(Y)`.  Its `C_0(X)`-structure is a continuous map
`pi:Y->X`, and `C_x=C_0(pi^(-1)(x))`.  Equation (10) makes every fibre of
`pi` contain at most one point, so `pi` is injective.

For each `y in Y`, choose a compact neighborhood `N`.  The restriction
`pi|N` is a continuous injection from a compact space to the Hausdorff space
`X`, hence a homeomorphism onto the compact subspace `pi(N)`.  Compact
subspaces of the zero-dimensional space `X` are zero-dimensional.  Thus
`Y` is locally zero-dimensional; second countability and local compactness
make covering dimension local here, so `dim(Y)=0`.  This proves the shadow
claim.
