---
rg: 2
id: returned-a2-native-arm-orbit-free-proof
kind: route
title: Amalgamate the returned Pauli packet with the native opposite-arm cell
target: returned-a2-native-arm-orbit-leaves-same-cut-pauli-free
requires:
  - returned-a2-window-leaves-same-cut-pauli-commutators-free
  - native-opposite-arm-return-has-finite-s6-model
---

Let `G_ret` be the finite group in
`returned-a2-same-cut-pauli-free-proof`.  It contains the literal
order-three word `V`, three returned parent-mark involutions

```text
M_i=V^i M_0 V^(-i),                 i in Z/3,          (1)
```

and the Pauli generators and projection `E` for which both equalities in
`(NAF2)` hold.  In particular `M_0` is nontrivial.

Let `G_nat<=S_6` be the finite model in
`native-opposite-arm-return-has-finite-s6-model`, and denote its final
parent-mark involution `Z_nat`.  Form the amalgamated free product

```text
Gamma=G_ret *_(<M_0>=<Z_nat>) G_nat.                  (2)
```

The normal-form theorem for amalgams embeds both vertex groups in `Gamma`.
Every relation from the returned-Pauli window therefore remains exact, and
every native fold--opposite-arm relation remains exact with its final mark
literally equal to the returned occurrence `M_0`.  Conjugating the embedded
copy of `G_nat` by `V^i` puts the identical table at `M_i`; no new generator
or independently chosen transporter is used for those two copies.

An amalgamated free product of finite groups is virtually free.  Hence
`Gamma` is residually finite.  Since `G_ret` is finite, take the product of
finitely many finite quotients separating all nonidentity elements of
`G_ret`.  This gives one homomorphism

```text
pi:Gamma -> F                                                   (3)
```

to a finite group whose restriction to `G_ret` is injective.  Use the left
regular representation of `F`.

All support terms in the expansion of `E`, `EX_1X_0`, and `EZ_1Z_0` lie in
`C[G_ret]`.  Injectivity of `pi|_(G_ret)` preserves which of those terms is
the identity.  Therefore the regular-trace computation from
`returned-a2-same-cut-pauli-free-proof` is unchanged:

```text
tau(E)=1/8,
tau_E(X_1X_0)=tau_E(Z_1Z_0)=0.                         (4)
```

Also `V` still transports `X_0,Z_0` to `X_1,Z_1` and commutes with `E`.
Equation `(4)` gives

```text
||[V,X_0]E||_(2,E)^2=||X_1-X_0||_(2,E)^2=2,
||[V,Z_0]E||_(2,E)^2=||Z_1-Z_0||_(2,E)^2=2.           (5)
```

Meanwhile all rows containing the uncancelled `s_0,t_0` occurrences are
exact in the embedded `G_nat` and its two `V`-conjugates.  Thus the enlarged
mixed menu has zero defect but both proposed same-word Pauli bounds have a
fixed maximal defect, proving the claim.

