---
rg: 2
id: toeplitz-parity-scalar-kernel-proof
kind: route
title: Transport zero parity trace to the self-centralizing Jacobson head
target: toeplitz-parity-negative-corner-has-trivial-scalar-kernel
requires:
  - rank-four-jacobson-head-retention-is-faithful
  - toeplitz-parity-compressor-candidate
---

For every `g in Lambda` with `chi(g)=1`, the parity relation gives

```text
pi(q)pi(g)pi(q)^*=-pi(g).
```

Taking trace yields `tau(g)=0`. In particular `tau(b)=0`. The stable-letter
relation gives

```text
pi(t)pi(b)pi(t)^*=pi(alpha(b))=pi(c),
```

so

```text
tau(c)=tau(b)=0.                                         (TPS2)
```

Here is the required projective-retention audit. In a tracial matrix
ultraproduct,

```text
|tr(u)|=1  iff  u is a scalar unitary.
```

Indeed

```text
||u-tr(u)1||_2^2=1-|tr(u)|^2.
```

Thus `(TPS2)` implies that `pi(c)` is not scalar. Compose the restriction to
`Gamma` with the projective quotient:

```text
bar_pi:Gamma -> U(M)/T.
```

Its kernel is exactly the scalar kernel of `tau|Gamma`, and
`bar_pi(c)!=1`. Since `c` is a nontrivial element of the finitary kernel,
`rank-four-jacobson-head-retention-is-faithful` makes `bar_pi` injective.
Therefore

```text
K_tau intersect Gamma=1.                                 (TPS3)
```

Every element outside `Gamma=ker chi` has `chi=1` and trace zero, hence
cannot belong to `K_tau`. Together with `(TPS3)` this proves `(TPS1)`.
