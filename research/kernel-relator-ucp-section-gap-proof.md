---
rg: 2
id: kernel-relator-ucp-section-gap-proof
kind: route
title: Accumulate Stinespring multiplicative-domain defects around one kernel cycle
target: kernel-relator-forces-two-edge-ucp-section-gap
requires:
  - triangle-colimit-llp-reduces-to-relator-local-splitting
---

The structural theorem supplies that `N` is a free group.  Hence every
`n in N\{1}` has infinite order.

Let `b_j=T(v_j)` and

```text
epsilon=max_j ||b_j-w_j||.
```

Every `b_j` is a contraction because `T` is ucp, while every `w_j` is
unitary.  Therefore

```text
||1-b_j b_j^*||
 = ||w_j w_j^*-b_j b_j^*|| <= 2 epsilon.                  (KUP1)
```

Choose a Stinespring representation `T(x)=V^* rho(x) V`, with `V` an
isometry and `P=VV^*`.  If `u` is unitary and `x` is a contraction, then

```text
T(ux)-T(u)T(x)=V^*rho(u)(1-P)rho(x)V,
```

and consequently

```text
||T(ux)-T(u)T(x)||
 <= ||V^*rho(u)(1-P)||
 =  ||1-T(u)T(u)^*||^(1/2).                               (KUP2)
```

Peel off `v_1,...,v_(L-1)` successively in `(KUP2)` and use `(KUP1)`:

```text
||T(v_1...v_L)-b_1...b_L|| <= (L-1) sqrt(2 epsilon).       (KUP3)
```

Since `q(n)=1`, the product `v_1...v_L` is `1`, and unitality gives
`T(v_1...v_L)=1`.  Telescoping the other product and using that all `b_j`
are contractions gives

```text
||b_1...b_L-w_1...w_L|| <= L epsilon.                      (KUP4)
```

The product of the `w_j` is `u_n`.  The canonical inclusion
`C^*(<n>)->C^*(E)` is faithful for the full group C-star algebra.  Since `n`
has infinite order, `C^*(<n>)=C(T)` and `u_n` has the full unit circle as
spectrum.  Hence `||1-u_n||=2`.  Combining `(KUP3)` and `(KUP4)` yields

```text
2 <= (L-1) sqrt(2 epsilon)+L epsilon.                       (KUP5)
```

Put `y=sqrt(epsilon)`.  The positive root of

```text
L y^2 + sqrt(2)(L-1)y - 2 = 0
```

is exactly `sqrt(2)/L`, because its discriminant is `2(L+1)^2`.
Thus `y>=sqrt(2)/L`, so `epsilon>=2/L^2`, proving `(KUG1)`.
