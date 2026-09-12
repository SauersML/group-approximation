---
rg: 2
id: a4-near-context-centralizer-product-rounding-proof
kind: route
title: Exactify the A4 triangle, align the order-three spectrum, and lift the involution orbit
target: a4-near-context-centralizer-product-rounding
requires:
  - a4-triangle-hs-regular-core
  - a4-regular-context-is-centralizer-product
---

Put `C_n=U_n B_n U_n^*`.  The pair `(A_n,C_n)` has exact orders three and
two, both nonidentity regular-character traces are zero, and its sole A4
relator defect tends to zero.  By `a4-triangle-hs-regular-core`, flexible
finite-group HS exactification produces, off `o(d_n)` dimensions, a regular
A4 representation whose named generators are `o(1)`-close in normalized HS
to `(A_n,C_n)`.

Because `A_n` is itself an exact multiple of the regular A4 generator, its
three spectral projections have equal rank.  The exactified order-three
generator has the same equal-rank pattern on its regular core.  The standard
finite-spectrum projection matching argument therefore changes the
exactification by an `o(1)`-HS unitary so that its order-three generator is
literally the restriction of `A_n` on a `12s_n`-dimensional regular summand.
Choose the summand so that `12s_n<=d_n` and `d_n-12s_n=o(d_n)`; the latter
difference is a multiple of twelve.  On the `A_n`-invariant complement fill in
copies of the canonical regular A4 representation.  The resulting exact pair

```text
(A_n,D_n)
```

is a full multiple of `Reg(A4)` on the original space and satisfies

```text
||D_n-C_n||_2 -> 0.                                   (1)
```

By `a4-regular-context-is-centralizer-product`, there is
`X_n in C_A,n` with

```text
D_n = X_n B_n X_n^*.
```

Set `V_n=X_n^*U_n`.  Equation (1) becomes

```text
||V_n B_n V_n^*-B_n||_2 -> 0.                         (2)
```

It remains only to lift the conjugacy-orbit estimate to the quotient by the
centralizer of `B_n`.  Put `P_n=(1+B_n)/2` and
`Q_n=V_n P_n V_n^*`.  They are projections of equal rank and (2) gives
`||P_n-Q_n||_2->0`.  The principal-angle construction for two equal-rank
projections supplies a unitary `W_n` with

```text
W_n Q_n W_n^*=P_n,
||W_n-1||_2 -> 0.
```

Hence `Y_n=W_n V_n` commutes with `P_n`, equivalently with `B_n`, so
`Y_n in C_B,n`; and

```text
||U_n-X_nY_n||_2
 = ||V_n-Y_n||_2
 = ||1-W_n||_2 -> 0.
```

Thus `dist_2(U_n,C_A,n C_B,n)->0`, as claimed.
