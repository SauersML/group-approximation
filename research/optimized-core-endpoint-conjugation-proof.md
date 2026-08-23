---
rg: 2
id: optimized-core-endpoint-conjugation-proof
kind: route
title: Move the BS core by the same conjugation and use the projected inversion row for the lower price
target: optimized-core-absorbs-endpoint-conjugations
requires: []
---

Because `z` commutes with `T`, conjugating the exact BS identity by `z`
gives

```text
(zRz^(-1))T(zR^(-1)z^(-1))=T^4.
```

Thus `c_z` belongs to the exact-core variety in `(GOI4)`. Equation `(OCA2)`
shows that every induced section edge for this competitor vanishes. The
`T` displacement is zero and the `R` displacement is the right side of
`(OCA3)`, proving that inequality exactly.

For `z=exp(i epsilon a)`, unitary-exponential Lipschitzness and `(LKP4)`
give

```text
||zRz^(-1)-R||_2=||z-psi(z)||_2<=epsilon g_L,
```

which proves `(OCA4)`.

For the lower price, let `W_epsilon=(X_zR)^2` and use the notation of
`low-koopman-endpoint-conjugation-counterpacket-proof`. Its calculation
before applying the inverse weight gives

```text
g_L^(-1)||P_(t_L) P_reg E_Z(W'_0)||_2
 >=1-2N^(-1/2).                                      (OCP1)
```

Conditional expectation and spectral projection are contractions, hence
the full inversion-row derivative has norm at least the left side times
`g_L`. For large `L` this is at least `g_L/2`; by finite-dimensional
differentiability, after reducing the positive `epsilon` threshold if
necessary,

```text
||(X_zR)^2-1||_2>=epsilon g_L/4.                      (OCP2)
```

The inversion row is one summand of `E_end`, so `(OCP2)` proves `(OCA5)`.

