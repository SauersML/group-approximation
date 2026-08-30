---
rg: 2
id: stw81-usc-af-fibre-localization-proof
kind: route
title: Lift AF fibre blocks through shrinking quotients and localize them by central cutoffs
target: stw81-af-fibre-fields-have-base-bound
requires: []
artifacts:
  - research/artifacts/stw81-usc-af-fibre-field-audit-2026-08-30.md
---

Put `n=dim(X)`.  Fix a finite self-adjoint set `F subset A` and
`epsilon>0`.  We construct an `(n+1)`-colour nuclear-dimension
approximation.

## 1. The fibre is a sequential neighborhood quotient

Second countability and local compactness make `X` metrizable and give each
`x in X` a decreasing neighborhood basis `(U_k)` such that

```text
K_k=closure(U_k) is compact,
K_(k+1) subset U_k,
intersection_k K_k={x}.
```

Set

```text
J_k=C_0(X minus K_k)A.
```

Then `J_k` increases and

```text
I_x=ker(A -> A_x)=closure(union_k J_k).                 (1)
```

To check density without any continuity-field assumption, first consider a
generator `fa` of `I_x`, where `f in C_0(X)` and `f(x)=0`.  Choose a scalar
cutoff `r_k` which is zero on `K_k` and one off `U_(k-1)`.  Since `f` is
small on a sufficiently small neighborhood of `x`, `r_k f -> f` uniformly,
and `(r_k f)a in J_k`.  Finite sums and closure prove (1).

## 2. A nonunital AF fibre still gives a c.p.c. retraction

Fix `x`.  If all elements of `F_x={a_x:a in F}` are already smaller than a
chosen tolerance, use the zero algebra.  Otherwise choose a
finite-dimensional subalgebra

```text
E_x subset A_x
```

which approximates `F_x`.  This does not require `A_x` or `E_x` to be
unital as a fibre algebra.  Let `p_x` be the unit of `E_x`.  Compression
`a -> p_x a p_x` maps `A_x` c.p.c. into `p_x A_x p_x`.  Finite-dimensional
C-star algebras are injective operator systems, so the identity on `E_x`
extends to a u.c.p. map

```text
Q_x:p_x A_x p_x -> E_x.
```

Consequently

```text
P_x(a)=Q_x(p_x a p_x):A_x -> E_x
```

is c.p.c. and fixes `E_x` pointwise.  Taking the initial approximation close
enough gives, for a parameter `delta>0`,

```text
||a_x-P_x(a_x)||<delta       for every a in F.           (2)
```

## 3. Semiprojectivity and upper semicontinuity

Let `eta_x:E_x -> A_x=A/I_x` be inclusion.  By (1) and semiprojectivity of
finite-dimensional C-star algebras, for some `k=k(x)` there is a
star-homomorphism

```text
sigma_x:E_x -> A/J_k
```

which composes to `eta_x` under `A/J_k -> A/I_x`.

For `a in F`, form in the restriction `A/J_k` the element

```text
b_(x,a)=sigma_x(P_x(a_x))-q_k(a).
```

By (2), `||(b_(x,a))_x||<delta`.  For every `C_0(X)`-algebra the function
`y -> ||b_y||` is upper semicontinuous.  Therefore, after shrinking inside
`U_k`, there is an open neighborhood `W_x` of `x` with

```text
closure(W_x) subset U_k,
||(b_(x,a))_y||<2delta
    for y in W_x and a in F.                             (3)
```

This is the only field-norm step; upper semicontinuity is exactly sufficient.

## 4. Coloured compact localization

Choose `h in C_c(X)_+`, `0<=h<=1`, with

```text
||a-ha||<epsilon/3       for a in F,                     (4)
```

and put `K=supp(h)`.  Finitely many `W_x` cover `K`.  Ostrand's
decomposable-refinement characterization of covering dimension for
metrizable spaces, followed by a finite shrinking, gives a finite refinement
`(V_i)` of a neighborhood of `K`, a colour map

```text
c(i) in {0,...,n},
```

and anchors `x(i)` such that

```text
closure(V_i) subset W_(x(i)),
closure(V_i) and closure(V_j) are disjoint when
    i!=j and c(i)=c(j).
```

Choose positive scalar functions `f_i` subordinate to `(V_i)` whose sum is
one on `K`, and set `g_i=hf_i`.  Then

```text
sum_i g_i=h,
supp(g_i) subset W_(x(i)),
g_i g_j=0 when i!=j and c(i)=c(j).                       (5)
```

## 5. The quotient-to-algebra localization is c.p.c. order zero

For the anchor of `i`, abbreviate `J=J_(k(x(i)))`, `E=E_(x(i))`, and
`sigma=sigma_(x(i))`.  Since `supp(g_i) subset U_(k(x(i))) subset K_(k(x(i)))`,
the completely positive contraction

```text
A -> A,       a -> g_i^(1/2) a g_i^(1/2)=g_i a
```

vanishes on `J`.  It therefore factors through a c.p.c. map

```text
L_(g_i):A/J -> A,       L_(g_i)(q(a))=g_i a.             (6)
```

Define

```text
psi_i(a)=P_(x(i))(a_(x(i))),
phi_i=L_(g_i) composed with sigma.
```

If `c,d in E_+` are orthogonal and `a,b` lift `sigma(c),sigma(d)`, then
`ab in J`; hence

```text
phi_i(c)phi_i(d)=g_i^2 ab=0.
```

Thus `phi_i` is c.p.c. order zero.  Equation (5) shows that the sum over any
one colour is order zero on the corresponding direct sum.

It remains to check contractivity of the return map, including the
nonunital case.  Let `p_i=sigma_i(1_(E_i))`, and choose a positive
contractive lift `e_i in A` of `p_i`.  In the multiplier order,

```text
phi_i(1_(E_i))=g_i e_i <= g_i 1_(M(A)).
```

Therefore the c.p. map

```text
phi:direct-sum_i E_i -> A,       phi=sum_i phi_i
```

satisfies

```text
phi(1)=sum_i phi_i(1_(E_i)) <= sum_i g_i=h<=1_(M(A)),
```

so `phi` is contractive.  The map

```text
psi=(psi_i)_i:A -> direct-sum_i E_i
```

is c.p.c. because each coordinate is c.p.c. and the finite direct sum has
the maximum norm.

## 6. Approximation

For `y in supp(g_i)`, estimate (3) applies.  Fibrewise, (5) gives

```text
||(ha-phi psi(a))_y||
 <= sum_i g_i(y)
       ||a_y-sigma_i(P_i(a_(x(i))))_y||
 <2delta.
```

Outside `supp(h)` both terms vanish.  Since the norm of an element of a
`C_0(X)`-algebra is the supremum of its fibre norms,

```text
||ha-phi psi(a)||<=2delta.                               (7)
```

Choose `2delta<2epsilon/3` and combine (4) and (7).  This proves
`dim_nuc(A)<=n`.

## 7. Simple non-elementary fibres are shadow-free

Assume every nonzero fibre `A_x` is simple and non-elementary.  Let `B=A/I`
be any quotient.  Its fibre at `x` is a quotient of `A_x` by the closed ideal
generated by the image of `I`; hence simplicity gives

```text
B_x=0 or B_x=A_x.                                      (8)
```

Suppose `C subset B` is a nonzero commutative hereditary subalgebra.  Choose
`0!=c in C_+` and `x` with `c_x!=0`.  The quotient image of the hereditary
algebra `Her_B(c)` is `Her_(B_x)(c_x)`, so it is a nonzero commutative
hereditary subalgebra of `B_x=A_x`.  It is full because `A_x` is simple.
Thus `A_x` is strongly Morita equivalent to a nonzero simple commutative
C-star algebra, and is therefore elementary, contradicting the hypothesis.
So every such `C` is zero.

In particular, if `n<=1`, the shadow hypothesis of Problem LXXXI holds and
the dimension bound above gives `dim_nuc(A) in {0,1}`.
