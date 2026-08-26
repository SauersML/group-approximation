---
rg: 2
id: odd-native-s-factor-return-diamond-has-gl7-model
kind: claim
title: The odd native s factor closes the returned-root diamond but still has a GL7 model
artifacts:
  - research/odd-native-s-factor-return-diamond-gl7-proof.md
  - experiments/odd_native_s_factor_return_diamond_gl7_audit.py
distinct_from:
  first-native-diamond-extension-of-cross-return-has-gl7-c2-model: that scoped table leaves the native actor as an independent GL7-C2 gauge because it does not contain the two odd coefficient factors of the literal Whitehead word; this adjoins those factors and proves that the C2 coordinate is then forced to vanish.
  non-equivariant-native-diamond-arm-matches-retain-gl7-c2-gauge: that matches the primed s00 and t00 arms separately without adjoining the odd factor x_87(s_00t_0); this forms that factor from one returned-root transport and closes its J1-conjugate diamond.
  center-chain-common-source-authenticates-native-covariances: that asks for a positive finite-matrix subcorner identifying both unequal selector transports with the nested Hecke polars; this only authenticates the literal first Whitehead factorization and ends in a finite exact marked model.
---

**ESTABLISHED ODD-FACTOR FINITE FENCE.**  In the first returned native
diamond write

```text
A=x_97(t_0),       B'=x_86(s_00),       M=x_96(1).
```

Adjoin the ordinary opposite root `bar M=x_69(1)` and its returned-root
Whitehead `P=M bar M M=w_96(1)`.  It swaps only the vertices `6,9` and
commutes with `J_1`.  Transporting the two named arms through `P` and then
using ordinary nonopposite Steinberg commutators gives

```text
PB'P=x_89(s_00),       PAP=x_67(t_0),
X=[PB'P,A]=[B',PAP]=x_87(s_00t_0).                    (OSF1)
```

Thus `X` is exactly the odd factor `X_1` of the literal native Whitehead,
not an analytic completion.  Conjugation by `J_1` closes the other side:

```text
J_1B'J_1=x_76(s_0)=B,
J_1AJ_1=x_98(t_00)=A',
PBP=x_79(s_0),         PA'P=x_68(t_00),
Y=[PBP,A']=[B,PA'P]=x_78(s_0t_00)=Y_1,
J_1XJ_1=Y_1.                                          (OSF2)
```

The coefficient reductions in `(OSF2)` are the two partial-Whitehead block
products

```text
(s_0t_00)s_00=s_0,       (1+s_00t_00)s_00=0,
t_0(s_1t_1)=0,           t_0(s_0t_00)=t_00.
```

Consequently the literal word relation

```text
J_1=X_1Y_1X_1                                             (OSF3)
```

does remove the external `C_2` factor retained by the earlier scoped
diamond.  In its `GL_7(F_2) times C_2` model the two odd roots have zero
`C_2` coordinate, while their `GL_7` matrices satisfy

```text
X_1Y_1X_1=(7_0 8_0).
```

Hence `(OSF3)` forces the `C_2` coordinate of `J_1` to be zero.

This is a genuine gauge improvement but not a marked obstruction.  The
complete extended table has an exact model in `GL_7(F_2)`: on the vertex
order

```text
(7_0,9,8_0,7_1,10,8_1,6)
```

take `bar M=e_(6,9)`, so `P=(6 9)` and `(OSF1)--(OSF3)` are elementary
path products and standard two-transvection swap identities.  Every preceding cross-return,
native-diamond, and non-equivariant arm-match row remains exact, whereas
the old marked child

```text
C_1=e_(7_1,8_1)
```

is still nonidentity.  Therefore the first odd `s_00t_0` occurrence kills
the artificial central sign but does not identify the native transport
with the unequal-scale Hecke reservoir and does not prove MF collapse.  A
live continuation must couple this now-authenticated `J_1` occurrence to a
second scale or to a coefficient-sensitive carrier outside this finite
`GL_7` closure.

No Property T, Kazhdan input, literature theorem, trace hypothesis, local
computation, or Lean compilation is used.

DERIVATION
odd-native-s-factor-return-diamond-gl7-proof
