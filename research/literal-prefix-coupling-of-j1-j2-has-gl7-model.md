---
rg: 2
id: literal-prefix-coupling-of-j1-j2-has-gl7-model
kind: claim
title: Literal prefix compilation couples J1 to J2 but closes in the same GL7 model
artifacts:
  - research/literal-prefix-j1-j2-coupling-gl7-proof.md
  - experiments/literal_prefix_j1_j2_coupling_gl7_audit.py
distinct_from:
  odd-native-s-factor-return-diamond-has-gl7-model: that authenticates the two factors and literal word of J1 and kills its external central sign; this uses the actual prefix equations to compile both factors of J2 from those of J1 and also imposes the adjacent native braid.
  support-return-charts-meet-in-two-pauli-pairs: that compares two transported support-return charts and retains an independent relative chart sign; this uses the literal coefficient factors of the native Whiteheads themselves, so both actor signs are removed, but the resulting adjacent swaps still form a finite S3 label action.
  center-chain-common-source-authenticates-native-covariances: that asks for unequal quarter/eighth selector typing on one positive finite-matrix subcorner; this authenticates the two native Whitehead words and their prefix relation only, and its finite model has two equal adjacent-swap label types.
---

**ESTABLISHED TWO-SCALE PREFIX FENCE.**  Write the literal native factors as

```text
X_1=x_87(x_1),       Y_1=x_78(y_1),
X_2=x_98(x_2),       Y_2=x_89(y_2),

x_1=s_00t_0,         y_1=s_0t_00,
x_2=s_000t_00,       y_2=s_00t_000.                  (LPJ1)
```

The second-scale coefficients are literal two-sided prefix refinements of
the first-scale coefficients:

```text
x_2=s_0x_1t_0,       y_2=s_0y_1t_0.                 (LPJ2)
```

Both identities have ordinary root-position compilations.  Put

```text
L_x=x_98(s_0),       R_x=x_78(t_0),
R_y=x_89(t_0),       L_y=x_87(s_0).
```

Then

```text
U=[L_x,X_1]=x_97(s_0x_1),       [U,R_x]=X_2,
V=[Y_1,R_y]=x_79(y_1t_0),       [L_y,V]=Y_2.          (LPJ3)
```

Thus the coupling is between the actual coefficient occurrences; it is
not a rank match or an analytic relabeling.  Impose the two literal
Whitehead words and their native adjacent braid:

```text
J_1=X_1Y_1X_1,       J_2=X_2Y_2X_2,
J_1J_2J_1=J_2J_1J_2.                                (LPJ4)
```

The resulting packet still has an exact finite marked model inside the
same `GL_7(F_2)` chart as the first odd-factor return.  On its vertices
`(7_0,9,8_0)` assign

```text
X_1=e_(8_0,7_0),     Y_1=e_(7_0,8_0),
X_2=e_(9,8_0),       Y_2=e_(8_0,9),                  (LPJ5)

L_x=X_2,             R_x=Y_1,
R_y=Y_2,             L_y=X_1.
```

The intermediate roots in `(LPJ3)` are respectively `e_(9,7_0)` and
`e_(7_0,9)`, so every root commutator is exact.  The two Whiteheads become
the adjacent transpositions

```text
J_1=(7_0 8_0),       J_2=(8_0 9),                    (LPJ6)
```

which satisfy the braid and generate a finite `S_3` subgroup.  The old
marked child `e_(7_1,8_1)` is on the other branch and remains nonidentity.

Consequently literal prefix coupling removes any independent central sign
from both native actors, but it does not distinguish their multiplicity
reservoirs or produce the unequal `1/4,1/8` selector rows.  In this finite
model the two actors are simply equal-type adjacent swaps.  A live next row
must attach one of these authenticated actors to a coefficient-sensitive
positive carrier or Hecke map that the `S_3` chart cannot realize; another
prefix compilation or the braid alone remains inside the finite closure.

This is a scoped model of the displayed ordinary-root occurrence table,
not a representation of the full binary Leavitt elementary group.  No
Property T, Kazhdan input, literature theorem, local computation, trace
hypothesis, or Lean compilation is used.

DERIVATION
literal-prefix-j1-j2-coupling-gl7-proof

