---
rg: 2
id: jacobson-residual-t-root-is-orthogonal-transport
kind: claim
title: The alternating Jacobson T-root transports the live residual orthogonally
artifacts:
  - research/jacobson-residual-t-root-orthogonality-proof.md
distinct_from:
  binary-jacobson-first-alternating-polar-is-half-supported: that computes the support of the T-root compression on the whole positive-tail range; this restricts to the final residual and proves the compression is exactly zero.
  binary-jacobson-native-v4-polar-orbit-leaves-one-residual: that locates the residual missed by the native polar orbit; this computes the action of the alternating T-root on that residual.
  binary-jacobson-first-alternating-ts-closure-relation: that derives the root x_21(T) from separately evaluated T-bearing and opposite-root occurrences; this shows that reducing those constituents to their product before compression loses all residual support.
---

Let `e=e_res` be the live positive-tail residual and put

```text
u=x_21(T),       d=x_13(S^2T),       r=x_23(ST).
```

The residual signs are

```text
d e=e,                 r e=-e.                          (JRO1)
```

The root commutator relation and `TS=1` give

```text
u d u=x_23(TS^2T)d=r d,          [u,r]=1.               (JRO2)
```

Consequently `u e u` lies in the negative spectral cut of `d`,
whereas `e` lies in its positive cut. Hence

```text
e u e=0,                 e(u e u)=0.                    (JRO3)
```

Thus the polar of the residual compression of the first alternating root is
zero, not a complementary coisometry. The unitary `u` merely transports
`e` to an orthogonal residual cell of the same rank.

For the qutrit packet this is also numerically neutral. Both `e` and
`u e u` are character cuts of order-`2^5` groups, so each has
canonical trace `1/32` and the same qutrit `2:1` mass profile. Bare
transport by `u` preserves that profile and creates no Hall deficit.

The first alternating relation can therefore remain load-bearing only with
its occurrence syntax intact: one must compress the separately evaluated
root `x_31(1)` jointly with the `T`-bearing constituent before replacing
their commutator by `u`, or use a different mixed square return. Any route
which first reduces the word to `x_21(T)` and then compresses to the live
residual is now ruled out exactly.
