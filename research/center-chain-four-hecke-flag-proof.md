---
rg: 2
id: center-chain-four-hecke-flag-proof
kind: route
title: Compute the four center-chain Hecke flags from their affine root orbits
target: center-chain-four-hecke-flags-have-native-ranks
requires:
  - center-chain-character-atom-gives-scalar-gram
  - center-chain-hecke-polar-supports-are-nested-pauli-flags
---

Write `h_3=x_65(q),h_2=x_54(q),h_1=x_42(q)` and let `chi(h_i)=-1`.
For an element `g`, character averaging of `ege` is controlled by the
affine `H`-orbit of `g`: if that orbit is `gW` for an elementary abelian
root group `W` on which the stabilizer characters agree, then

```text
ege=egz_W,             (ege)^*(ege)=ez_W.              (1)
```

For `B_2=x_84(b_2)`, only `h_1=x_42(q)` produces a new root coordinate,
namely

```text
[B_2,h_1]=x_82(b_2).
```

Consequently `H.B_2=B_2D_1` with
`D_1=<x_82(b_2)>` of order two.  Formula `(1)` gives

```text
eB_2e=eB_2z_(D_1),       supp|eB_2e|=ez_(D_1),
tau(supp|eB_2e|)=tau(e)/2.                              (2)
```

For `B_3=x_95(b_3)`, the center-chain coordinates `h_2=x_54(q)` and the
derived root `x_52(q)=[h_2,h_1]` produce the two independent roots

```text
x_94(b_3),                     x_92(b_3).
```

The remaining commutators only permute their span.  Hence
`H.B_3=B_3D_2`, where

```text
D_2=<x_94(b_3),x_92(b_3)> ~= F_2^2.
```

Again `(1)` yields

```text
eB_3e=eB_3z_(D_2),       supp|eB_3e|=ez_(D_2),
tau(supp|eB_3e|)=tau(e)/4.                              (3)
```

The A-side calculations are the already established affine orbit formulas

```text
H.A_1=A_1<x_57(a_1),x_67(a_1)>,
H.(A_2A_1)=A_2A_1<x_57(a_1),x_67(a_1),x_68(a_2)>.
```

Applying `(1)` gives the last two supports in `(FHF2)` and their relative
traces `1/4` and `1/8`.  Finally `B_3B_2` detects the direct sum of the
one-dimensional `B_2` coordinate and the two-dimensional `B_3` coordinate,
so the cumulative B-orbit has size eight and its support fraction is `1/8`.
This proves all assertions.
