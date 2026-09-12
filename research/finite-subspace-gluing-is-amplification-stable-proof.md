---
rg: 2
id: finite-subspace-gluing-is-amplification-stable-proof
kind: route
title: Tensor the positive Friedrichs-angle operator with the identity
target: finite-subspace-gluing-is-amplification-stable
requires: []
---

Let `P_i` be the orthogonal projection of `E` onto `M_i` and set

```text
A=sum_i (I-P_i).
```

Then `A` is positive semidefinite and

```text
ker(A)=intersection_i ker(I-P_i)=M.
```

Because `E` is finite dimensional, the restriction of `A` to `M^perp` has a
smallest positive eigenvalue `lambda>0`.  Hence

```text
lambda ||(I-P_M)x||^2
 <= <Ax,x>
 = sum_i ||(I-P_i)x||^2.                              (1)
```

Now amplify by any finite-dimensional `K`.  The orthogonal projections onto
`M_i tensor K` and `M tensor K` are respectively `P_i tensor I_K` and
`P_M tensor I_K`, while the positive operator controlling the sum of squared
distances is exactly

```text
A tensor I_K.
```

Its nonzero spectrum is the nonzero spectrum of `A`, repeated
`dim(K)` times.  In particular its smallest positive eigenvalue is still the
same `lambda`, independent of the amplification.  Tensoring `(1)` therefore
gives

```text
dist(x,M tensor K)^2
 <= lambda^(-1) sum_i dist(x,M_i tensor K)^2.
```

Take `C=lambda^(-1)`.  The Hilbert--Schmidt operator-space version is the same
argument after identifying the fixed base operator space with a finite
Hilbert space.