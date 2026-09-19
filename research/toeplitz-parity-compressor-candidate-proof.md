---
rg: 2
id: toeplitz-parity-compressor-candidate-proof
kind: route
title: Put an involutive swap in the finite head and kill the external parity in the tail
target: toeplitz-parity-compressor-candidate
requires:
  - toeplitz-head-tail-unital-self-embedding
  - toeplitz-finite-head-centralizes-deep-tail
  - toeplitz-tail-plus-one-swap-generates
  - parity-headed-compressor-kills-mark-in-exact-matrix-models
---

Let `sigma:T->T` be the proper unital head-tail embedding and take depth
`N=2`.  The head swap

```text
s=1+e_00+e_11+e_10+e_01
```

satisfies `s^2=1`, belongs to the unitization of the head algebra `F_2`, and
commutes with `sigma^2(T)`.  It does not belong to `sigma^2(T)`: every
element of the tail acts by a scalar on the first two head coordinates,
whereas `s` transposes them.

Put `c=s I_4`.  The standard elementary identity

```text
diag(u,u^(-1)) in EL_2(R),       u in R^x,
```

applied to two diagonal blocks and to `u=s=s^(-1)` shows that
`c in EL_4(T)`.  Since `s` centralizes `sigma^2(T)`, `c` centralizes the
entrywise image

```text
beta(Gamma)=EL_4(sigma^2(T)).
```

Also `c notin beta(Gamma)`, because its diagonal entry `s` is not in the
tail ring.  Entrywise `sigma^2` is injective, so `beta` is injective.

Write the external `C_2` additively and define

```text
alpha(g,epsilon)=(beta(g)c^epsilon,0),
chi(g,epsilon)=epsilon.                                    (TPC1)
```

Centralization makes `alpha` a homomorphism.  If its value is trivial, then
`beta(g)=c^epsilon`; injectivity of `beta` handles `epsilon=0`, while
`c notin beta(Gamma)` excludes `epsilon=1`.  Hence `alpha` is injective, and
`chi alpha=0` is immediate.

The ring `T` is finitely generated, so the Ershov--Jaikin-Zapirain theorem
gives property `(T)` for `EL_4(T)`; finite direct products preserve it.
The matrix group is finitely generated and computably presented, hence so is
the HNN construction.  This proves all assertions.

