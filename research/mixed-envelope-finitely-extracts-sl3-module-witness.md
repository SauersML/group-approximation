---
rg: 2
id: mixed-envelope-finitely-extracts-sl3-module-witness
kind: claim
title: A successful mixed envelope contains a finite SL3-module nonhyperlinear witness
distinct_from:
  haagerup-factor-direction-strips-from-property-t-envelope: that removes the Haagerup actor direction and may leave an infinitely generated module over the complementary actor; this extracts a finitely generated recursively presented complementary submodule.
  algebraic-compact-action-group-factor-compiler: that compiles the whole supplied module; this proves that finite module data inside a successful mixed construction already suffices, though it does not identify the first successful finite stage in advance.
---

Let `Gamma` be Haagerup, let `H` be finitely generated and recursively
presented, and let `A` be a countable recursively presented
`F_p[Gamma x H]`-module.  Suppose a non-Connes-embeddable property-`(T)`
`II_1` factor embeds trace-preservingly in

```text
L(A rtimes (Gamma x H)).                                (MFE1)
```

Then there are finitely many elements `a_1,...,a_m in A` such that the
`F_p[H]`-submodule

```text
A_0 = F_p[H] a_1 + ... + F_p[H] a_m                    (MFE2)
```

satisfies

```text
A_0 rtimes H is non-hyperlinear.                        (MFE3)
```

Moreover `A_0 rtimes H` is finitely generated and recursively presented.
It therefore embeds by Higman's theorem in a finitely presented group, which
is necessarily non-hyperlinear.

For `Gamma=Gamma_Manzoor` and `H=SL_3(Z)`, any successful finitely generated
r.e. mixed module thus contains a finite `SL_3(Z)`-module witness and already
implies a finitely presented non-hyperlinear group.  Mixing with the Manzoor
direction cannot hide the obstruction solely in an infinitely generated
`SL_3` restriction.
